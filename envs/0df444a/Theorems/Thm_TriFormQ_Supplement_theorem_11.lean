-- Prove2me | Theorems.Thm_TriFormQ_Supplement_theorem_11
-- name    : TriFormQ.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:01:03.672374+00:00
-- url     : https://prove2.me/theorems/8e55ab35-3d51-4b36-a277-3c2f1fb251d0
-- title:
--   Theorem 11 — some family of $L$ trilinear forms needs $\Omega_q(\log^{2/3}L)$ quantum queries to identify
-- statement:
--   Let $\mathbb F_q$ be a finite field. There is a constant $c=c(q)>0$ such that for every integer $L\ge2$ there exist a dimension $m$ and $L$ **distinct** trilinear forms $f_1,\dots,f_L$ on $\mathbb F_q^m\times\mathbb F_q^m\times\mathbb F_q^m$ with the following property. Every randomized quantum query algorithm with oracle access $O_f:|x,y,z,b\rangle\mapsto|x,y,z,b+f(x,y,z)\rangle$ that, for every $i\in[L]$, outputs $i$ with probability at least $2/3$ when the hidden form is $f_i$, has some $i$ for which a run of positive probability on $O_{f_i}$ makes at least
--
--   $$c\cdot(\log_2 L)^{2/3}$$
--
--   queries. Equivalently, an algorithm making at most $t$ queries on every computational path and identifying the hidden member of the family with probability $\ge2/3$ has $t=\Omega_q(\log^{2/3}L)$.
--
--   This is the formal version of Theorem 3 (p.4) and shows that the dependence on $L$ in the main theorem (the mission's goal) cannot be improved in general.
--
--   **Formalization Note** Algorithms are the base mission's `AdaptiveAlg` (intermediate measurements and classical randomness allowed), the oracle is the base `oracle`, and "$t$ queries on every computational path" is `maxQueries`. The constant must depend on $q$: for $L\le q$ one query identifies $f_i=a_ix_1y_1z_1$ with distinct $a_i$.
--
--   Differences from the source:
--   - encoding: $\Omega(\log^{2/3}L)$ → one constant $c>0$ depending only on $\mathbb F_q$, chosen before $L$, with $(\log_2L)^{2/3}$; reason: the meaning of $\Omega_q$, logarithms base 2 (p.10).
--   - encoding: "a family $\{f_i\}_{i\in[L]}$ of trilinear forms" → an injective map $f:[L]\to$ trilinear forms on $\mathbb F_q^m$, $m$ chosen with $L$; reason: identification among $L$ forms presupposes $L$ distinct forms (p.44: "any set of $L$ distinct trilinear forms"); requiring distinctness only constrains the witness.
--   - encoding: "succeeding in identifying the hidden form with probability $\ge 2/3$", "$t$ queries on every computational path" → for every $i$, `outProb` of output $i$ on $O_{f_i}$ at least $2/3$; conclusion `maxQueries` $\ge c(\log_2L)^{2/3}$ on some $O_{f_i}$; reason: the bounded-error guarantee for every hidden member and the worst-case path length.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 11, p.42 (PDF p.45); informal Theorem 3, p.4 (PDF p.7); proof pp.42–44

import Definitions.Def_TriFormQ_oracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries

namespace TriFormQ.Supplement

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 11, p.42 (PDF p.45):
"For any integer L ≥ 2, there exists a family of trilinear forms
F = {f_i : 𝔽_q^m × 𝔽_q^m × 𝔽_q^m → 𝔽_q}_{i∈[L]} such that any quantum query algorithm making t
queries on every computational paths and succeeding in identifying the hidden form f ∈ F with
probability ≥ 2/3 must make t = Ω(log^{2/3} L) many queries." Informal version: Theorem 3, p.4
(PDF p.7).

**Formalization Note.** For every finite field `F` (`q = |F|`) there is one constant `c > 0`,
chosen before `L` (the `Ω` depends on `q` only; it cannot be uniform in `q`, since for `L ≤ q`
one query identifies `f_i = a_i x₁y₁z₁`). The dimension `m` may depend on `L`. The family is `L`
**distinct** trilinear forms (an injective `f : Fin L → TriForm F m`). The algorithm is any
`TriFormQ.AdaptiveAlg` (intermediate measurements and classical randomness allowed) with the
standard oracle; "succeeding with probability ≥ 2/3" is: for every `i`, it outputs `i` with
probability at least `2/3` on the oracle of `f_i`. "Making t queries on every computational path"
is `maxQueries ≤ t` on every oracle of the family, so the conclusion is that some member's oracle
forces at least `c · (log₂ L)^{2/3}` queries. Logarithms base 2 (p.10). -/
theorem theorem_11 :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], ∃ c : ℝ, 0 < c ∧ ∀ L : ℕ, 2 ≤ L →
      ∃ (m : ℕ) (f : Fin L → TriForm F m), Function.Injective f ∧
        ∀ A : AdaptiveAlg (Vec F m × Vec F m × Vec F m) F (Fin L),
          (∀ i : Fin L, (2 : ℝ) / 3 ≤ A.outProb (oracle (f i)) (fun j => j = i)) →
          ∃ i : Fin L, c * (Real.logb 2 L) ^ ((2 : ℝ) / 3) ≤ (A.maxQueries (oracle (f i)) : ℝ) := by sorry

end TriFormQ.Supplement
