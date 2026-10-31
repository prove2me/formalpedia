-- Prove2me | Theorems.Thm_RainsSep_Distill_theorem2_sep_distillable_le
-- name    : RainsSep.Distill.theorem2_sep_distillable_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:50.689291+00:00
-- url     : https://prove2.me/theorems/9c759429-3f20-47eb-87b9-83cc12786a64
-- title:
--   Theorem 2: $D_*(f)\le 1-H_2(f)$ for the depolarizing state, and higher rates force fidelity $\to 0$
-- statement:
--   Let $\tfrac12\le f\le1$ and let $\Delta_f=\Delta\big(\tfrac43(1-f)\big)$ be the depolarizing two-qubit state with entanglement fidelity $f$. Let $H_2(f)=-f\log_2f-(1-f)\log_2(1-f)$. Then:
--
--   1. every separably achievable rate $R$ for $\Delta_f$ satisfies
--
--   $$
--   R\le 1-H_2(f)=1+f\log_2 f+(1-f)\log_2(1-f),
--   $$
--
--   that is, $D_*(f)\le 1-H_2(f)$;
--
--   2. for every sequence of separable superoperators $\mathcal P_i$ from two $n_i$-qubit registers to $\mathbb C^{K_i}\otimes\mathbb C^{K_i}$ with $n_i\to\infty$ and, for some $R>1-H_2(f)$, $\log_2K_i/n_i\ge R$ for all large $i$,
--
--   $$
--   \lim_{i\to\infty}F\big(\mathcal P_i(\Delta_f^{\otimes n_i})\big)=0 .
--   $$
--
--   Since every LOCC protocol is separable, the bound applies to the two-way distillable entanglement $D_2(f)$ and improves on the entanglement-of-formation bound for $\tfrac12<f<1$.
--
--   Differences from the source:
--   - reading: f ≥ 1/2, Δ(ε) "the depolarizing state with fidelity f" → 1/2 ≤ f ≤ 1; reason: Δ with fidelity f is a state only for f ≤ 1
--   - reading: D∗(f) ≤ 1 − H₂(f), D∗ "the largest number" with properties (3)–(4) → every R with AchievableSepRate (Δ_f) R satisfies R ≤ 1 − H₂(f); reason: the set formulation is the definition; it avoids a supremum in ℝ (which would be 0 on an unbounded set)
--   - reading: P_i maps states on V^{⊗n_i} to states on W_i, rate log₂ dim W_i / n_i → P_i maps n_i copies of the bipartite state to a K_i × K_i bipartite state, rate log₂ K_i / n_i, n_i ≥ 1; reason: as the proof of Theorem 2 says ("producing a K_i × K_i bipartite state from n_i + n_i qubits"); n_i ≥ 1 only excludes an undefined rate
--   - reading: "any family of separable superoperators of rate greater than 1 − H₂(f)" → sequences with n_i → ∞ whose rate log₂ K_i / n_i is eventually ≥ some R > 1 − H₂(f); reason: the proof takes n_i → ∞ ("as n increases"); without it the clause is false (n_i = 1, K_i = 4, discard the input and prepare |00⟩: fidelity 1/4 at rate 2)
--   - generalization: the rate log₂ K_i / n_i tends to a limit greater than 1 − H₂(f) → the rate is eventually ≥ some R > 1 − H₂(f) (liminf above the bound); reason: a sequence with such a limit eventually exceeds any R strictly between the bound and the limit
--   - encoding: a separable superoperator has a product Kraus representation Σ_i (unspecified index set) → IsSeparableSuperop asks for a finite product Kraus family indexed by Fin m; reason: in finite dimension every separable superoperator has a finite product representation (its Choi matrix lies in the finite-dimensional separable cone, Carathéodory), so nothing is excluded
--   - encoding: V an n-qubit space, W of dimension K, an orthonormal basis, a bipartite V ⊗ V → Qubits n (bit strings of length n, false = |0⟩), W = Fin K, the first tensor factor Alice's, her qubit k paired with Bob's qubit k, computational bases, fidelity the real part of φ+† σ φ+; reason: a choice of labels: φ+ depends on the basis only up to local unitaries (p. 1), and the value is real on Hermitian operators
--   - encoding: H₂(f), written out by Eq. (41) → binEntropy2 f = Real.binEntropy f / Real.log 2; Eq. (41) is a conjunct of clause 1 with Real.logb 2; reason: the paper defines H₂ only through (41); at f = 1 the junk value Real.logb 2 0 = 0 gives the convention 0 log 0 = 0
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Theorem 2, Eqs. (40)–(41), p. 3; proof pp. 3–4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_RainsSep_Distill_depolarizingOfFidelity
import Definitions.Def_RainsSep_Distill_AchievableSepRate

open QAlgorithms Filter Topology

namespace RainsSep.Distill

/-- **Theorem 2: `D∗(f) ≤ 1 − H₂(f)`, and higher rates force fidelity → 0.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Theorem 2, Eqs. (40)–(41), p. 3: "Let f ≥ 1/2. The separably distillable entanglement D∗(f)
of the depolarizing state ∆(ǫ) with fidelity f, satisfies the bound D∗(f) ≤ 1 − H2(f) (40)
= 1 + f log2(f) + (1 − f) log2(1 − f). (41) Indeed, any family of separable superoperators of rate
greater than 1 − H2(f) must have output fidelity tending to 0." Proof pp. 3–4.

For every `f` with `1/2 ≤ f ≤ 1`, writing `Δ_f = Δ((4/3)(1 − f))`:
1. every separably achievable rate `R` from `Δ_f` satisfies `R ≤ 1 − H₂(f)`, and
   `1 − H₂(f) = 1 + f log₂ f + (1 − f) log₂ (1 − f)` (Eq. (41));
2. for every sequence of separable superoperators `P_i` from `n_i` qubit pairs to
   `ℂ^{K_i} ⊗ ℂ^{K_i}` with `n_i → ∞` and `log₂ K_i / n_i ≥ R` eventually, for some
   `R > 1 − H₂(f)`, the output fidelity `F(P_i(Δ_f^{⊗n_i}))` tends to `0`.

**Formalization Note.** `f ≤ 1` is the range in which `Δ_f` is a state. In (2), "rate greater
than `1 − H₂(f)`" is taken as `liminf log₂ K_i / n_i > 1 − H₂(f)` (a limit is not required), and
`n_i → ∞` is assumed, as in the proof ("as n increases"); without it the clause fails (`n_i = 1`,
`K_i = 4`, discard-and-prepare `|00⟩`: fidelity `1/4`, rate `2`). Clause (1) keeps the
definition of achievable rates without `n_i → ∞`. `H₂` is `binEntropy2` (bits). -/
theorem theorem2_sep_distillable_le (f : ℝ) (hf0 : 1 / 2 ≤ f) (hf1 : f ≤ 1) :
    ((∀ R : ℝ, AchievableSepRate (depolarizingOfFidelity f) R → R ≤ 1 - binEntropy2 f) ∧
        1 - binEntropy2 f = 1 + f * Real.logb 2 f + (1 - f) * Real.logb 2 (1 - f)) ∧
      ∀ (n K : ℕ → ℕ)
        (P : ∀ i, Superop (Qubits (n i) × Qubits (n i)) (Fin (K i) × Fin (K i))),
        (∀ i, IsSeparableSuperop (P i)) → Tendsto n atTop atTop →
        (∃ R > 1 - binEntropy2 f, ∀ᶠ i in atTop, R ≤ Real.logb 2 (K i) / n i) →
        Tendsto (fun i => entFidelity (P i (pairPower (depolarizingOfFidelity f) (n i))))
          atTop (𝓝 0) := by sorry

end RainsSep.Distill
