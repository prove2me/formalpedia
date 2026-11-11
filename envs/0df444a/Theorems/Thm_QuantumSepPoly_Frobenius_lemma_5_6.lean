-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_5_6
-- name    : QuantumSepPoly.Frobenius.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:25.3012+00:00
-- url     : https://prove2.me/theorems/36f376aa-74af-46e1-b573-40c37e1dca56
-- title:
--   Lemma 5.6 — Support-function approximation by the CSP
-- statement:
--   Let $M$ be Hermitian with $\|M\|_F\le1$, $0<\eta<1$, and $0<\delta<1/2$. Apply the actual reduction using unitary $U,V$, conditioned on the successful computed tail test. Put $D=\Pi(C_{\rm flat})$, $\alpha=\operatorname{Tr}M/d^2$, and let $I$ and $s$ be its constructed CSP and scale. If $d\ge\Delta$, then
--   $$\left|h_{\rm Sep}(M)-\left(\alpha+2s(\operatorname{OPT}(I)-\tfrac12)\right)\right|\le\delta+\eta+2/\sqrt d.$$
--   This preserves both sides of the support approximation.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: the successful flat decomposition output and its CSP → the computed threshold decomposition, its tail test, projection, net, and CSP; reason: no approximation guarantee is assumed for an arbitrary unrelated CSP
--   - generalization: the fixed cutoff data from Lemma 3.3 → any cutoff data on its successful computed tail event; reason: the support estimate uses the computed tail bound and projection; all source successful outputs are included
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 5.6, p. 21 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_CSPReduction

namespace QuantumSepPoly.Frobenius

/-- Lemma 5.6, p.21. Both sides of the error bound are preserved. -/
theorem lemma_5_6 (p : FlatParameters) (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1/2) (d : ℕ) (hd : 0 < d) (M : Bip d) (U V : Op d)
    (hM : M.IsHermitian) (hF : frob M ≤ 1)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsuccess : flattenSuccess p δ (centered M) U V)
    (hdim : discDelta (reductionGamma (reductionD p δ M U V)) η ≤ d) :
    let D := reductionD p δ M U V
    let γ := reductionGamma D
    |support M - ((alpha M).re + 2*cspScale γ η * (cspOPT (reductionInstance hd D η) - 1/2))| ≤
      δ + η + 2/Real.sqrt (d : ℝ) := by sorry

end QuantumSepPoly.Frobenius
