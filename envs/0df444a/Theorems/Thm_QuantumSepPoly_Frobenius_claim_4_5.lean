-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_claim_4_5
-- name    : QuantumSepPoly.Frobenius.claim_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:09.930194+00:00
-- url     : https://prove2.me/theorems/4b8bf5a4-c5ed-42b8-93c7-77ac1360b74f
-- title:
--   Claim 4.5 — Normalization of the penalized objective
-- statement:
--   Let $M$ satisfy the Section 4 flatness and zero-partial-trace assumptions. Let $E$ be a finite $\varepsilon$-net contained in the closed radius-$\kappa$ disk, with $\varepsilon,\lambda>0$, and $x,y\in E^d$. Normalize each to norm $\sqrt d$, replacing a zero vector with $\sqrt d\,u_1$. Then
--   $$Q_M(\widetilde x,\widetilde y)\ge\Lambda_M(x,y)-(\gamma^2+\gamma^2\kappa^4)/(4\lambda).$$
--   This controls the error when returning a normalized feasible pair.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: normalize to sqrt(d), replacing the zero vector by sqrt(d)u1 → normalizeSqrt uses the squared norm zero test and the first Fin-indexed basis vector; reason: the test is equivalent to a zero vector and the resulting normalization is identical
--   - generalization: the parameters selected in the proof of Lemma 4.4 → any disk radius and finite contained net with positive mesh and any positive penalty weight; reason: the displayed estimate uses only the amplitude bound and positive penalty weight; the selected source parameters satisfy these conditions
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Claim 4.5, p. 18 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_DiskNet

namespace QuantumSepPoly.Frobenius

/-- Claim 4.5, p.18. The normalization includes the zero-vector branch on p.17. -/
theorem claim_4_5 (d : ℕ) (hd : 0 < d) (M : Bip d) (γ κ ε lam : ℝ)
    (hM : FlatInput M γ) (hε : 0 < ε) (hlam : 0 < lam)
    (E : Finset ℂ) (hE : IsDiskNet E κ ε) (x y : Vec d)
    (hx : ∀ i, x i ∈ E) (hy : ∀ i, y i ∈ E) :
    Q M (normalizeSqrt x) (normalizeSqrt y) ≥ penalty M lam x y - (γ^2+γ^2*κ^4)/(4*lam) := by sorry

end QuantumSepPoly.Frobenius
