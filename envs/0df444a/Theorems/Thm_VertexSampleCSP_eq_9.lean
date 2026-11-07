-- Prove2me | Theorems.Thm_VertexSampleCSP_eq_9
-- name    : VertexSampleCSP.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:27.896965+00:00
-- url     : https://prove2.me/theorems/8f4ce66d-6ac3-49b0-bd2b-2b96fac0a1e3
-- title:
--   Display (9), p.15 — $B\Delta=\sum_iZ_i$, $\rho^{-1}B\Delta_S=\rho^{-1}\sum_{i\in S}Z_i$, $\sum_{i,a}\|c_{ia}\|^2=\frac{1}{r\cdot r!}\sum_i\gamma_i^2/t_i$
-- statement:
--   Fix an instance on $V$ and positive weights on the relevant variables, and let $c_{ia}=Be_{ia}$, $Z_i=\mathrm{conv}\{c_{ia}:a\in[q]\}$. Then:
--
--   1. $B\Delta=\sum_{i\in V}Z_i$ (Minkowski sum);
--   2. $\rho^{-1}B\Delta_S=\rho^{-1}\sum_{i\in S}Z_i$ for every $\rho>0$ and $S\subseteq V$;
--   3. the squared norm of $B$ is
--
--   $$\sum_{i,a}\|c_{ia}\|^2=\frac{1}{r\cdot r!}\sum_{i\text{ relevant}}\frac{\gamma_i(\mathcal I)^2}{t_i}.$$
--
--   These identities place the image sets in the form of Lemma C.1 and connect its $\Lambda$ with the scale $\Gamma$.
--
--   **Formalization Note** The Minkowski sum over a finite index set is a sum of sets under pointwise addition, and the empty sum is $\{0\}$, as on p.13.
--
--   Differences from the source:
--
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: Σ‖c_ia‖² = ‖B‖² = (1/(r·r!)) Σ γ_i²/t_i → the outer equality only; reason: ‖B‖² is by definition the squared Hilbert–Schmidt norm Σ_{i,a}‖Be_ia‖², so the middle equality is that definition
--   - encoding: positive weights t_i for the relevant variables → t : V → ℝ with 0 < t i whenever γ_i > 0; reason: values on irrelevant variables are never read
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), display (9), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_Instance_Gamma
import Definitions.Def_VertexSampleCSP_DeltaS
import Definitions.Def_VertexSampleCSP_tensorEntry
import Definitions.Def_VertexSampleCSP_flatten
import Definitions.Def_VertexSampleCSP_weightedFlatten
open scoped Pointwise

namespace VertexSampleCSP

/-- **Display (9) (the image sets are Minkowski sums).** Chang, *Optimal Vertex Sampling for
Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix B,
display (9), p.15 (PDF p.17): "Let cia = Beia and Zi = conv{cia : a ∈ [q]}. Then B∆ = Σ_{i∈V} Zi,
ρ^{−1}B∆S = ρ^{−1} Σ_{i∈S} Zi, Σ_{i,a} ∥cia∥² = ∥B∥² = (1/(r · r!)) Σ_{i relevant} γi(I)²/ti."

Fix positive weights `t_i` on the relevant variables and let `c_{ia} = B e_{ia}`,
`Z_i = conv{c_{ia} : a ∈ [q]}`.
1. `BΔ = Σ_{i ∈ V} Z_i` (Minkowski sum).
2. For every `ρ > 0` and `S ⊆ V`: `ρ⁻¹BΔ_S = ρ⁻¹ Σ_{i ∈ S} Z_i`.
3. `Σ_{i,a} ‖c_{ia}‖² = (1/(r·r!)) Σ_{i relevant} γ_i(I)²/t_i`.

**Formalization Note.** The Minkowski sum over a finite index set is `Finset.sum` of sets under
pointwise addition; the empty sum is `{0}`, as on p.13. `‖B‖²` is by definition the squared
Hilbert–Schmidt norm `Σ_{i,a} ‖B e_{ia}‖²`, so the middle equality of the third clause is that
definition and the clause states the outer equality. -/
theorem eq_9 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r) (hq : 0 < q)
    (I : Instance V r q) (t : V → ℝ) (ht : ∀ i, 0 < I.gamma i → 0 < t i) :
    weightedFlatten I t '' DeltaS V q Finset.univ = ∑ i, genPolytope I t i ∧
    (∀ (ρ : ℝ), 0 < ρ → ∀ S : Finset V,
      ρ⁻¹ • (weightedFlatten I t '' DeltaS V q S) = ρ⁻¹ • ∑ i ∈ S, genPolytope I t i) ∧
    ∑ i, ∑ a, ‖genVec I t i a‖ ^ 2 =
      1 / ((r : ℝ) * (r.factorial : ℝ)) *
        ∑ i ∈ Finset.univ.filter (fun i => 0 < I.gamma i), I.gamma i ^ 2 / t i := by sorry

end VertexSampleCSP
