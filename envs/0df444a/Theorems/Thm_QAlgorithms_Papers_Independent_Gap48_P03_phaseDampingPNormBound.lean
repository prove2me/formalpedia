-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_phaseDampingPNormBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.phaseDampingPNormBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:59:43.617365+00:00
-- url     : https://prove2.me/theorems/11e129ac-b0f5-4fa2-ac43-56f180dd1978
-- title:
--   Phase-damping norm bound with unnormalized conditional blocks
-- statement:
--   Let $d\ge2$, $m\ge1$, and $-1/(d-1)\le\lambda\le1$. Let $B=(u_i)_{i=1}^d$ be any orthonormal basis, $E_i=|u_i\rangle\langle u_i|$, and $\Phi_{\lambda,B}(X)=\lambda X+(1-\lambda)\sum_i E_iXE_i$. For an arbitrary state $\rho$ on $\mathbb C^d\otimes\mathbb C^m$, set $R_i=\operatorname{Tr}_1[(E_i\otimes I)\rho]$. Put $a=\lambda+(1-\lambda)/d$, $b=(1-\lambda)/d$, and $v_p=(a^p+(d-1)b^p)^{1/p}$. For every real $p\ge1$,
--
--   $$\|(\Phi_{\lambda,B}\otimes I)(\rho)\|_p\le d^{1-1/p}v_p\left(\sum_{i=1}^d\operatorname{Tr}(R_i^p)\right)^{1/p}.$$
--
--   The $R_i$ are unnormalized positive conditional blocks and can have zero trace. The recalled factor $v_p$ is the explicit spectral expression, so this statement uses the full phase-damping interval without assuming the raw depolarizing map is CPTP there.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 11, Lemma 9: phase-damping p-norm bound using unnormalized conditional blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

namespace QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0204172v2, PDF p.11, Lemma 9, (33)-(34).
Use the full phase interval and unnormalized conditional blocks. The recalled nu factor
is expression (10); the raw Delta is not assumed CPTP on the larger interval. -/
theorem phaseDampingPNormBound {d m : ℕ} (hd : 2 ≤ d) (hm : 0 < m)
    (lam : ℝ) (hlow : -1 / ((d : ℝ) - 1) ≤ lam) (hhigh : lam ≤ 1)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (rho : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) (hrho : IsDensityMatrix rho)
    (p : ℝ) (hp : 1 ≤ p) :
    schatten p (QAlgorithms.Papers.Independent.Information100.P63.phaseDamping
      (1 - lam) (U : Matrix (Fin d) (Fin d) ℂ) rho) ≤
      (d : ℝ) ^ (1 - 1 / p) * depolarizingNormFactor d lam p *
        (∑ i, (cfc (fun x : ℝ => x ^ p)
          (block (U : Matrix (Fin d) (Fin d) ℂ) rho i i)).trace.re) ^ (1 / p) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
