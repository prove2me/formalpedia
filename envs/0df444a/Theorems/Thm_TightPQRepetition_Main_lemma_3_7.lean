-- Prove2me | Theorems.Thm_TightPQRepetition_Main_lemma_3_7
-- name    : TightPQRepetition.Main.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:42:58.679815+00:00
-- url     : https://prove2.me/theorems/9480f7ba-34a7-4eb6-8284-8816c3d46888
-- title:
--   Lemma 3.7 — minimal-subverifier preprocessing (corrected: $t'=0$ only when $t=0$, and $k\ge1$)
-- statement:
--   Let $(P,V)$ be a protocol with an efficient verifier and $\widehat V$ its encrypted version under an efficient scheme. There is a transformation $T$ such that, for all $1\le k$, $t\le k$, $\nu\in(0,1]$, $\varepsilon\in[0,1]$ and every prover $B$ against $\widehat V^{k,t}$:
--
--   1. $T(1^\lambda,t,k,\nu,\varepsilon)$ runs in time $\mathrm{poly}(\lambda,k,\nu^{-1})$ given oracle access to $B$, and outputs a set $S\subseteq[k]$ of size $k'\in[1,k]$, a threshold $t'\le t$ with $t'\ge1$ if $t\ge1$, and query coins $r^*$; the adversary $A=A_S$ has the core of $B$ and a polynomial classical overhead.
--
--   2. If $\Pr[\langle B,\widehat V^{k,t}\rangle(1^\lambda)=1]\ge B(k,t,\varepsilon)+\nu$, then with probability at least $1-2^{-\lambda}$ the output satisfies
--   $$\Pr[\langle A,\widehat V^{k',t'}\rangle(1^\lambda)=1]\ge B(k',t',\varepsilon)+\frac{10k'-1}{10k}\nu,$$
--   and either $k'=1$, or the conditional tail bounds of `TailBounds` hold for $A$ on a $1-\nu/10k$ fraction of $r^*$.
--
--   This lemma reduces the proof to a single-copy case and to a prover whose first coordinate has no bad correlation with the others.
--
--   Differences from the source:
--   - generalization: PPT verifier and encryption algorithms (uniform) → non-uniform families of polynomial-size Boolean circuits, with coins an explicit input and outputs of bounded, input-dependent length; reason: a uniform PPT algorithm gives such a family, so every source instance is covered; the source already takes all adversaries non-uniform (Remark 5.2)
--   - encoding: QPT prover with quantum advice → a family of `Strategy`: a pure advice state, one unitary circuit of one- and two-qubit gates per round, computational-basis measurement of answer wires, and a polynomial-size classical controller with a random tape; reason: purification costs polynomial overhead (PDF p. 22); the source fixes no gate set
--   - correction: t′ ∈ [t], k′ ∈ [k] for all t ≤ k ∈ ℕ → k ≥ 1, t′ ≤ t, and t′ ≥ 1 whenever t ≥ 1; reason: [0] is empty, so literally T has no output at t = 0 or k = 0; for t ≥ 1 the printed range holds because t′ = 0 would force success above 1
--   - reading: ν ∈ [0,1], running time poly(λ,k,ν⁻¹) → ν ∈ (0,1]; reason: at ν = 0 the bound and M₁, M₂ of Appendix A.1 are undefined, while Lean's 0⁻¹ = 0 would claim something else
--   - generalization: T outputs an adversary A using poly(λ,k) copies of B's initial state → T outputs (S, t′, r*) and A is the explicit A_S, with exactly the core of B and one copy; reason: this is the adversary of the proof and implies the printed form
--   - encoding: T runs given oracle access to B; A runs in time poly(λ,k) → T asks for fresh executions of B with chosen coins and sees the answers, its circuits polynomial in λ, k, 1/ν and input length; A's classical overhead is polynomial in λ, k, its input length and the cost of B's controller; reason: this is how the proof uses B; messages have polynomial length
--   - generalization: the scheme is a QFHE of Definition 2, or an FHE of Definition 1 for Remark 3.3 → any `EncScheme`: efficient classical Gen, Enc, Dec with semantic security, with no homomorphic evaluation or correctness required; reason: the verifier and the soundness proof use only these; `ClassicalFHE.toEncScheme` and `QFHE.toEncScheme` give the source's two cases
--   - reading: queries q_j of unspecified length → each q_j has a length depending only on λ and j; reason: the dummy Enc(0) of Algorithm 1 is prepared before the query is known, and semantic security needs |m₀| = |m₁|, so the length must be known in advance; a verifier reaches this form by padding
--   - reading: a transformation T(1^λ, t, k, ν, ε), an algorithm → polynomial-size circuits indexed by the discrete inputs (λ, t, k, ⌈1/ν⌉), reading ν and ε only through (P+2)-bit dyadic approximations to precision 2^{-P}, for a polynomial precision P of T's choice; the guarantees hold for every such approximation; reason: the source does not say how an algorithm receives the reals ν, ε; reading them through approximations at requested precision is the standard convention and gives one circuit for all ν, ε with the same discrete inputs. Non-uniformity in λ is that of the model, where V and the scheme are non-uniform; non-uniformity in t ≤ k and ⌈1/ν⌉, given in unary, is equivalent to one circuit per input length up to a polynomial factor
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 3.7, printed p. 12 / PDF p. 14; proof Appendix A.1, printed pp. 35–36 / PDF pp. 37–38

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Preprocess

namespace TightPQRepetition.Main

/-- Lemma 3.7 (printed p. 12, PDF p. 14; proof PDF pp. 37–38). -/
theorem lemma_3_7 (E : EncScheme) (hE : E.IsEfficient) (V : Verifier) (hV : V.IsEfficient) :
    ∃ T : Preprocessor, T.IsEfficient ∧
      (∃ q : ℕ → ℕ, PolyBound q ∧
        ∀ (p : PreParams) (o : PreOutput) (B : Strategy) (s : ℕ → ℕ),
          o.IsWellFormed V p → Monotone s → B.ControllerCost s →
          (simAdversary E V p.lam p.k B o).size ≤ B.size + q (p.lam + p.k) ∧
          (simAdversary E V p.lam p.k B o).ControllerCost
            (fun n => q (p.lam + p.k + n + s (q (p.lam + p.k + n))))) ∧
      ∀ (p : PreParams) (B : Strategy), B.Valid → 1 ≤ p.k → p.t ≤ p.k → 0 < p.ν → p.ν ≤ 1 →
        0 ≤ p.ε → p.ε ≤ 1 → ∀ aν aε : Bits,
        IsApprox p.ν (T.prec p.index) aν → IsApprox p.ε (T.prec p.index) aε →
        T.outputProb E V p aν aε B (fun o => o.IsWellFormed V p) = 1 ∧
        (binomTail p.k p.t p.ε + p.ν ≤ B.acceptProb (hatPar E V p.k p.t) p.lam →
          1 - (1 / 2 : ℝ) ^ p.lam ≤
            T.outputProb E V p aν aε B (fun o => o.IsGood E V B p)) := by sorry

end TightPQRepetition.Main
