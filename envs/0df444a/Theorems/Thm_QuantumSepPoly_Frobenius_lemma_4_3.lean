-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_4_3
-- name    : QuantumSepPoly.Frobenius.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:10.055148+00:00
-- url     : https://prove2.me/theorems/1eaa3d37-0f9a-4690-8e2f-9743f1e05d07
-- title:
--   Lemma 4.3 — Penalized continuity
-- statement:
--   Under the hypotheses of the quartic continuity estimate, let $\lambda>0$ and $\Lambda_M(x,y)=Q_M(x,y)-\lambda(\|x\|_2^2/d-1)^2-\lambda(\|y\|_2^2/d-1)^2$. Then
--   $$|\Lambda_M(x,y)-\Lambda_M(w,z)|\le4\gamma\kappa^3\varepsilon+8\lambda\kappa(\kappa^2+1)\varepsilon.$$
--   This retains the full penalty contribution to the continuity bound.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 4.3, p. 17 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Quartic

namespace QuantumSepPoly.Frobenius

/-- Lemma 4.3, p.17, with every standing assumption from pp.13,16. -/
theorem lemma_4_3 (d : ℕ) (hd : 0 < d) (M : Bip d) (γ κ ε lam : ℝ)
    (hM : FlatInput M γ) (hε : 0 < ε) (hlam : 0 < lam)
    (w x y z : Vec d) (hw : AmplitudeBound κ w) (hx : AmplitudeBound κ x)
    (hy : AmplitudeBound κ y) (hz : AmplitudeBound κ z)
    (hxw : CloseCoordinates ε x w) (hyz : CloseCoordinates ε y z) :
    |penalty M lam x y - penalty M lam w z| ≤ 4*γ*κ^3*ε + 8*lam*κ*(κ^2+1)*ε := by sorry

end QuantumSepPoly.Frobenius
