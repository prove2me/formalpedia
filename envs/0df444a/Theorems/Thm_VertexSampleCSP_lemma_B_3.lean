-- Prove2me | Theorems.Thm_VertexSampleCSP_lemma_B_3
-- name    : VertexSampleCSP.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:40.269102+00:00
-- url     : https://prove2.me/theorems/06a7a97f-1b6e-48b2-ac4b-a47068199066
-- title:
--   Lemma B.3, p.15 — transfer: $|\rho^{-r}\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)|\le\sigma_r(\rho)\sqrt\tau N^{(r-2)/2}d_H(B\Delta,\rho^{-1}B\Delta_S)$
-- statement:
--   Fix an instance on $V$ with $N=|V|$ and positive weights on the relevant variables. For every $S\subseteq V$ and $0<\rho\le1$,
--
--   $$\big|\rho^{-r}\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)\big|\le\sigma_r(\rho)\sqrt\tau\,N^{(r-2)/2}\,d_H\big(B\Delta,\rho^{-1}B\Delta_S\big).$$
--
--   The inequality holds for every $S$, including the sample that determines the optimum, so the randomness of the estimator is reduced to one geometric quantity.
--
--   **Formalization Note** $B\Delta$ and $B\Delta_S$ are images under the linear map $B$. With $q\ge1$ they are nonempty and compact, so `Metric.hausdorffDist` is the paper's $d_H$.
--
--   Differences from the source:
--
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: I[S] is the instance on S → I.sub S on the subtype ↥S; reason: same instance, written in a type with |S| variables
--   - encoding: positive weights t_i for the relevant variables → t : V → ℝ with 0 < t i whenever γ_i > 0; reason: values on irrelevant variables are never read
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma B.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_OPT
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_Instance_Gamma
import Definitions.Def_VertexSampleCSP_DeltaS
import Definitions.Def_VertexSampleCSP_tensorEntry
import Definitions.Def_VertexSampleCSP_flatten
import Definitions.Def_VertexSampleCSP_weightedFlatten
import Definitions.Def_VertexSampleCSP_sigmaR
open scoped Pointwise

namespace VertexSampleCSP

/-- **Lemma B.3 (Transfer).** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*,
STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma B.3, p.15 (PDF p.17): "For every S ⊆ V
and 0 < ρ ≤ 1, |ρ^{−r} OPT(I[S]) − OPT(I)| ≤ σr(ρ) √τ N^{(r−2)/2} dH(B∆, ρ^{−1}B∆S)."

Fix positive weights `t_i` on the relevant variables, with `B` and `τ` as in Appendix B, and
`N = |V|`. For every `S ⊆ V` and `0 < ρ ≤ 1`,
`|ρ^{−r} OPT(I[S]) − OPT(I)| ≤ σ_r(ρ) √τ N^{(r−2)/2} d_H(BΔ, ρ⁻¹BΔ_S)`.

**Formalization Note.** `BΔ` and `BΔ_S` are the images of `Δ` and `Δ_S` under the linear map `B`;
with `q ≥ 1` they are nonempty and compact, so `Metric.hausdorffDist` is the paper's `d_H`. `I[S]` is
the instance on the subtype `↥S`. -/
theorem lemma_B_3 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r) (hq : 0 < q)
    (I : Instance V r q) (t : V → ℝ) (ht : ∀ i, 0 < I.gamma i → 0 < t i)
    (S : Finset V) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    |(ρ ^ r)⁻¹ * OPT (I.sub S) - OPT I| ≤
      sigmaR r ρ * Real.sqrt (tauW I t) * (Fintype.card V : ℝ) ^ (((r : ℝ) - 2) / 2) *
        Metric.hausdorffDist (weightedFlatten I t '' DeltaS V q Finset.univ)
          (ρ⁻¹ • (weightedFlatten I t '' DeltaS V q S)) := by sorry

end VertexSampleCSP
