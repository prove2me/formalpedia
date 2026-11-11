-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_5_5
-- name    : QuantumSepPoly.Frobenius.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:19.760246+00:00
-- url     : https://prove2.me/theorems/8b17599c-4f14-41d0-8bb2-519949294964
-- title:
--   Lemma 5.5 — CSP value identity
-- statement:
--   For the explicit four-slot construction with matrix $D$, parameter $\eta$, and each assignment $z_i=(x_i,y_i)$ in its finite alphabet,
--   $$\operatorname{val}_I(z)=\tfrac12+\Lambda_D(x,y)/(2s).$$
--   The algebraic identity holds for any complex $D$ and any real parameter in the total formulas. In the source application $D$ is precisely the projected flat part. This relates the CSP average to the penalized objective.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - generalization: the projected Hermitian flat part at valid reduction accuracy → any complex matrix and any real accuracy parameter in the same algebraic construction; reason: taking real parts preserves the value identity, including every source construction
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 5.5, p. 20 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_CSPReduction

namespace QuantumSepPoly.Frobenius

/-- Lemma 5.5, p.20. The D supplied to this identity is the projected flat part
in the source application; the algebraic identity holds for every complex matrix. -/
theorem lemma_5_5 (d : ℕ) (hd : 0 < d) (D : Bip d) (η : ℝ)
    (z : Fin d → ReductionSymbol (reductionGamma D) η) :
    cspValue (reductionInstance hd D η) z = 1/2 +
      penalty D (discLambda (reductionGamma D) η) (fun i => (z i).val.1)
        (fun i => (z i).val.2) / (2*cspScale (reductionGamma D) η) := by sorry

end QuantumSepPoly.Frobenius
