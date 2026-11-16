-- Prove2me | Theorems.Thm_SelectedSubset3SUM_Integer_Supplement_theorem_3_4
-- name    : SelectedSubset3SUM.Integer.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:51:28.808998+00:00
-- url     : https://prove2.me/theorems/ad690b12-4cb6-4b22-b22a-7bb19a8fcfba
-- title:
--   Theorem 3.4 — conditional unbalanced integer 3SUM reduction to convolution on $[r]^d$
-- statement:
--   Let $\rho(r)=r^2/(r!)^{1/r}$.
--
--   1. There are constants $c_1,c_2,c_3>0$ with $c_1r\le\rho(r)\le c_2r$ and $1-\log_{\rho(r)}r\le c_3/\log r$ for every integer $r\ge2$.
--   2. Fix an integer $r\ge2$ and suppose one program solves every real-weight instance of Problem 3.1 over $[r]^d$ (every $d$, every split $t_1+t_2=t$) within $O(P(n,d,t,r)+|\mathcal C|\,Q(n,d,t,r))$ total time, with $P,Q\ge0$. Then for every exponent $\kappa$ there are one randomized word-RAM program, constants $b,e$, $K>0$, a dimension function $D(|A|,|B|)$ and a step budget $T(|A|,|B|,|C|)$ such that:
--      - for nonempty sides, $(r-1)D$ is even and $\bigl|D-2\log_\rho\widehat n\bigr|\le K\,(1+\lg\lg\max(2,N))$;
--      - for all duplicate-free $A,B,C\subseteq[N^\kappa]$, where $N=|A|+|B|$ and $\widehat n=\sqrt{|A||B|}$, with $d=D(|A|,|B|)$ and $t=(r-1)d/2$, the total charge is at most
--      $$K\,(\lg\max(2,N)+1)^e\;\widehat n^{\,2(1-\log_\rho r)}\Bigl(P(N,d,t,r)+N+|C|\bigl(Q(N,d,t,r)+1\bigr)\Bigr),$$
--      and, at every word width at least $b(\lfloor\lg\max(2,N)\rfloor+1)$, the program halts within the budget on every coin tape, and the probability that it rejects or answers some query "$c\in A+B$?" ($c\in C$) wrongly is at most $K/N$. When $A$ or $B$ is empty the answers are always correct and the charge is at most $K(|A|+|B|+|C|+1)$.
--
--   The sizes $|A|$, $|B|$, $|C|$ are arbitrary and independent; all hashing, sampling, repetitions, all rank splits, and the simulation of the real-weight solver on integer data are part of the conclusion.
--
--   Combined with Theorem 3.3 this gives Corollary 3.5 (query cost $\widehat n^{O(1/\log(1/\varepsilon))}$) and the $(2k+1)$-SUM algorithm of Corollary 3.6.
--
--   Differences from the source:
--   - generalization: a Problem 3.1 solver with cost O(P + |C|Q) (for all bases) → a solver for the fixed base r only; reason: a solver for every base restricts to the fixed constant r, so this weaker premise specializes to the source's
--   - reading: Problem 3.1 can be solved in O(P(n,d,t,r) + |C|Q(n,d,t,r)) time → one uniform program on the scalar machine with exact division by words, correct on every real-weight instance, every d and every split t₁+t₂ = t, charge (input, outputs, steps) at most K(P + |C|Q), P,Q ≥ 0; reason: the source's solver is real-weight; its integer realisation in the reduction is a proof obligation, not assumed
--   - reading: A, B, C ⊆ [n^{O(1)}] → A, B, C ⊆ [N^κ] for every fixed κ, N = |A|+|B|; reason: n is unbound in the statement; the proof uses log N and Corollary 3.5 on p.14 states [N^{O(1)}]
--   - reading: d = 2 log_ρ n̂ + O(log log N), t = (r−1)d/2 → a dimension function D(|A|,|B|), fixed with the program, with (r−1)D even and |D − 2 log_ρ n̂| ≤ K(1 + lg lg max(2,N)) for nonempty sides; t = (r−1)D/2; reason: the O-term is a choice made by the algorithm (p.14 chooses ρ^d ≈ 4n̂² lg² N); its parity makes t a natural number
--   - encoding: Õ(n̂^{2(1−log_ρ r)}(P + N + |C|(Q+1))) with error probability O(1/N) → a uniform power of 1+lg max(2,N) times that expression, a size-dependent worst-case step budget on every coin tape, and probability at most K/N of the event that some query answer is wrong or the run rejects; empty sides answered exactly within |A|+|B|+|C|+1; reason: the joint failure event covers all queries; at an empty side n̂ = 0 and the expression is undefined in the source's sense, and the answer is trivially all no
--   - encoding: ρ = Θ(r), 1 − log_ρ r = O(1/log r) → constants c₁,c₂,c₃ > 0 with c₁r ≤ ρ(r) ≤ c₂r and 1 − log_ρ r ≤ c₃/log r for all r ≥ 2; reason: the uniform reading of the two asymptotic remarks in r
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Theorem 3.4, p.12 (proof pp.12–14, inheriting the truncation and amplification of the proof of Theorem 2.3, pp.8–9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Definitions.Def_SelectedSubset3SUM_Integer_Supplement_Vector

namespace SelectedSubset3SUM.Integer.Supplement

open SelectedSubset3SUM.Integer

/-- Theorem 3.4, p.12 (proof pp.12--14). First clause: the remarks `ρ = Θ(r)` and
`1 - log_ρ r = O(1/log r)`, uniformly in `r ≥ 2`. Second clause: for every constant base
`r ≥ 2`, a real-weight Problem 3.1 solver of cost `O(P(n,d,t,r) + |𝒞| Q(n,d,t,r))` yields, for
every magnitude exponent `κ`, one randomized word-RAM program that answers every query of an
arbitrary (unbalanced) instance `A, B, C ⊆ [N^κ]` with joint error `O(1/N)` in
`Õ(n̂^{2(1 - log_ρ r)} (P(N,d,t,r) + N + |C| (Q(N,d,t,r) + 1)))` time, `t = (r-1)d/2`, at a
dimension `d = D(|A|,|B|)` with `d = 2 log_ρ n̂ + O(log log N)`. Empty sides get exact answers
in linear time. The integer realisation of the real solver is a proof obligation. -/
theorem theorem_3_4 (P Q : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ ∀ r : ℕ, 2 ≤ r →
      c₁ * r ≤ rho r ∧ rho r ≤ c₂ * r ∧ 1 - Real.logb (rho r) r ≤ c₃ / Real.log r) ∧
    ∀ r : ℕ, 2 ≤ r → VecSolver r P Q →
      ∀ κ : ℕ, ∃ (code : List TrulySubcubicAPSP.Instr) (b e : ℕ) (K : ℝ)
        (D : ℕ → ℕ → ℕ) (T : ℕ → ℕ → ℕ → ℕ),
        0 < b ∧ 0 < K ∧
        (∀ a₁ a₂ : ℕ, 1 ≤ a₁ → 1 ≤ a₂ →
          (r - 1) * D a₁ a₂ % 2 = 0 ∧
          |(D a₁ a₂ : ℝ) - 2 * Real.logb (rho r) (Real.sqrt ((a₁ * a₂ : ℕ) : ℝ))| ≤
            K * (1 + lg (lg (max 2 (a₁ + a₂ : ℕ))))) ∧
        ∀ I : SumInput, I.Valid κ →
          (sumCharge 0 (T I.A.length I.B.length I.C.length) I : ℝ) ≤
            K * polylogFactor I.N e *
              vecReductionCost r P Q I (D I.A.length I.B.length) ∧
          ∀ W ≥ b * (Nat.log2 (max 2 I.N) + 1),
            MonteCarloAt code W 0 (T I.A.length I.B.length I.C.length) K I := by sorry

end SelectedSubset3SUM.Integer.Supplement
