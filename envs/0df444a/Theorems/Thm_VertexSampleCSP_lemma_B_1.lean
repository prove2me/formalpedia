-- Prove2me | Theorems.Thm_VertexSampleCSP_lemma_B_1
-- name    : VertexSampleCSP.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:41.924198+00:00
-- url     : https://prove2.me/theorems/9f24cdb2-8381-4558-a46a-a739d258559b
-- title:
--   Lemma B.1, p.14 — relaxation: $\max_{y\in\rho^{-1}\Delta_S}P(y)=\rho^{-r}\mathrm{OPT}(\mathcal I[S])$
-- statement:
--   Fix an instance $\mathcal I$ of arity $r$ over $[q]$ on $V$. For every $S\subseteq V$ and $\rho>0$,
--
--   $$\max_{y\in\rho^{-1}\Delta_S}P(y)=\rho^{-r}\,\mathrm{OPT}(\mathcal I[S]),$$
--
--   and the maximum is attained. So the optimum of a subinstance is the maximum of a single polynomial over a convex body, and the two optima of the estimator can be compared on the same polynomial.
--
--   Differences from the source:
--
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: I[S] is the instance on S → I.sub S on the subtype ↥S; reason: same instance, written in a type with |S| variables
--   - encoding: max → IsGreatest of the image, so attainment is part of the claim; reason: the printed max is attained
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma B.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_OPT
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_DeltaS
import Definitions.Def_VertexSampleCSP_tensorEntry
open scoped Pointwise

namespace VertexSampleCSP

/-- **Lemma B.1 (Relaxation).** Chang, *Optimal Vertex Sampling for Constraint Satisfaction
Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma B.1, p.14 (PDF p.16), in the
setting of Appendix B ("Fix an instance I of arity r over [q] on a set V of N variables, with the
encoding of Appendix A"): "For every S ⊆ V and ρ > 0, max_{y∈ρ^{−1}∆S} P(y) = ρ^{−r} OPT(I[S])."

The maximum of the polynomial `P(y) = T[y, …, y]` over the scaled product of simplices `ρ⁻¹Δ_S` is
attained and equals `ρ^{−r} OPT(I[S])`.

**Formalization Note.** "max" is stated as `IsGreatest` of the image, so attainment is part of the
claim. `I[S]` is the instance on the subtype `↥S`. `[q]` is `Fin q` with `q ≥ 1`. -/
theorem lemma_B_1 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r) (hq : 0 < q)
    (I : Instance V r q) (S : Finset V) (ρ : ℝ) (hρ : 0 < ρ) :
    IsGreatest (poly I '' (ρ⁻¹ • DeltaS V q S)) ((ρ ^ r)⁻¹ * OPT (I.sub S)) := by sorry

end VertexSampleCSP
