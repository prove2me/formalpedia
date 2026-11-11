-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_4_2
-- name    : QuantumSepPoly.Frobenius.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:50.765886+00:00
-- url     : https://prove2.me/theorems/c2e1d52f-61bb-4095-883b-6311b519ea0d
-- title:
--   Lemma 4.2 — Quartic continuity
-- statement:
--   Let $M$ be a Section 4 flat Hermitian matrix with both partial traces zero and $d^2\|M\|_{\max}\le\gamma$. Suppose $w,x,y,z$ have infinity norm at most $\kappa$, $\varepsilon>0$, and $\|x-w\|_\infty,\|y-z\|_\infty\le\varepsilon$. Then
--   $$|Q_M(x,y)-Q_M(w,z)|\le4\gamma\kappa^3\varepsilon.$$
--   This is the exact quartic continuity estimate.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 4.2, p. 16 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Quartic

namespace QuantumSepPoly.Frobenius

/-- Lemma 4.2, p.16, with the standing assumptions of Section 4. -/
theorem lemma_4_2 (d : ℕ) (hd : 0 < d) (M : Bip d) (γ κ ε : ℝ)
    (hM : FlatInput M γ) (hε : 0 < ε)
    (w x y z : Vec d) (hw : AmplitudeBound κ w) (hx : AmplitudeBound κ x)
    (hy : AmplitudeBound κ y) (hz : AmplitudeBound κ z)
    (hxw : CloseCoordinates ε x w) (hyz : CloseCoordinates ε y z) :
    |Q M x y - Q M w z| ≤ 4*γ*κ^3*ε := by sorry

end QuantumSepPoly.Frobenius
