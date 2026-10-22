-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_qubitIdentities
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.qubitIdentities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:03:09.009027+00:00
-- url     : https://prove2.me/theorems/43a9bea4-9c61-4ab3-b902-390b72f937e3
-- title:
--   Qubit identities and the two-channel intermediate average
-- statement:
--   Let $-1/3\le\lambda\le1$, $\lambda_\pm=(1\pm\lambda)/2$, and let $\rho=\begin{pmatrix}a&c\\\overline c&b\end{pmatrix}$ be a density matrix on $\mathbb C^2$. Let $\sigma_x,\sigma_y,\sigma_z$ be the standard Pauli matrices, $G=\operatorname{diag}(-1,1)=-\sigma_z$, $H=\operatorname{diag}(e^{\pi i/4},-1)$, and $\tau=\begin{pmatrix}0&e^{\pi i/4}\\e^{-\pi i/4}&0\end{pmatrix}$. Write $\overline\tau$ for its entrywise conjugate and $\operatorname{Ad}(V)(X)=VXV^*$. Define the family $\Phi^{(a)}$ from the columns $G^kH^a(1,1)/\sqrt2$, $k=1,2$, by the phase-damping formula (27). Then
--
--   $$\Delta_\lambda(\rho)=\begin{pmatrix}\lambda_+a+\lambda_-b&\lambda c\\\lambda\overline c&\lambda_-a+\lambda_+b\end{pmatrix},\quad \Omega_\lambda(\rho)=\begin{pmatrix}\lambda_+a+\lambda_-b&\lambda_+c\\\lambda_+\overline c&\lambda_-a+\lambda_+b\end{pmatrix}.$$
--
--   As maps on states, $\Phi^{(2)}=\Phi^{(6)}=\lambda_+\mathrm{id}+\lambda_-\operatorname{Ad}(\sigma_y)$, $\Phi^{(4)}=\Phi^{(8)}=\lambda_+\mathrm{id}+\lambda_-\operatorname{Ad}(\sigma_x)$, $\Phi^{(1)}=\Phi^{(5)}=\lambda_+\mathrm{id}+\lambda_-\operatorname{Ad}(\tau)$, and $\Phi^{(3)}=\Phi^{(7)}=\lambda_+\mathrm{id}+\lambda_-\operatorname{Ad}(\overline\tau)$. Moreover,
--
--   $$\Omega_\lambda=\tfrac18\sum_{a=1}^8\Phi^{(a)}=\tfrac12(\Phi^{(2)}+\Phi^{(4)}),\qquad \Delta_\lambda=\frac{2\lambda}{1+\lambda}\Omega_\lambda+\frac{1-\lambda}{2(1+\lambda)}(\Omega_\lambda+\operatorname{Ad}(\sigma_z)\circ\Omega_\lambda).$$
--
--   Consequently, with $w=(1+3\lambda)/(4(1+\lambda))$ and $v=(1-\lambda)/(4(1+\lambda))$, the four-term formula is $\Delta_\lambda=w(\Phi^{(2)}+\Phi^{(4)})+v(\operatorname{Ad}(\sigma_z)\circ\Phi^{(2)}+\operatorname{Ad}(\sigma_z)\circ\Phi^{(4)})$. It supplies the source’s reduced decomposition with nonnegative weights throughout the qubit CPTP interval.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 16, Unnumbered qubit formulas (73)–(85), including the two-channel Ωλ decomposition

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

/-- King quant-ph/0204172v2, PDF pp.16-18, (73)-(85).
Normalized states, complex off-diagonal conjugation, and the two-channel Omega average.
The four Delta terms are output-conjugated phase-damping maps. -/
theorem qubitIdentities (lam : ℝ) (hlow : -1 / 3 ≤ lam) (hhigh : lam ≤ 1) :
    let lp : ℂ := ((1 + lam) / 2 : ℝ)
    let lm : ℂ := ((1 - lam) / 2 : ℝ)
    let sx := qubitPauli pauliX
    let sy := qubitPauli pauliY
    let sz := qubitPauli pauliZ
    clockUnitary 2 = -sz ∧
    quadraticPhaseUnitary 2 = !![Complex.exp ((Real.pi : ℂ) * Complex.I / 4), 0; 0, -1] ∧
    ∀ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix rho →
      let a := rho 0 0
      let b := rho 1 1
      let c := rho 0 1
      depolarizing 2 (1 - lam) rho = !![lp*a + lm*b, (lam : ℂ)*c;
        (lam : ℂ)*conj c, lm*a + lp*b] ∧
      intermediateChannel 2 lam rho = !![lp*a + lm*b, lp*c; lp*conj c, lm*a + lp*b] ∧
      depolarizing 2 (1 - lam) rho = (((2*lam/(1+lam) : ℝ) : ℂ)) • intermediateChannel 2 lam rho +
        ((((1-lam)/(2*(1+lam)) : ℝ) : ℂ)) •
          (intermediateChannel 2 lam rho + conjSuperop sz (intermediateChannel 2 lam rho)) ∧
      constructedPhaseDamping 2 lam 2 rho = constructedPhaseDamping 2 lam 6 rho ∧
      constructedPhaseDamping 2 lam 2 rho = lp • rho + lm • conjSuperop sy rho ∧
      constructedPhaseDamping 2 lam 4 rho = constructedPhaseDamping 2 lam 8 rho ∧
      constructedPhaseDamping 2 lam 4 rho = lp • rho + lm • conjSuperop sx rho ∧
      constructedPhaseDamping 2 lam 1 rho = constructedPhaseDamping 2 lam 5 rho ∧
      constructedPhaseDamping 2 lam 1 rho = lp • rho + lm • conjSuperop qubitTau rho ∧
      constructedPhaseDamping 2 lam 3 rho = constructedPhaseDamping 2 lam 7 rho ∧
      constructedPhaseDamping 2 lam 3 rho = lp • rho + lm • conjSuperop qubitTauConjugate rho ∧
      intermediateChannel 2 lam rho = (1/8 : ℂ) •
        (∑ a : Fin 8, constructedPhaseDamping 2 lam (a.val+1) rho) ∧
      intermediateChannel 2 lam rho = (1/2 : ℂ) •
        (constructedPhaseDamping 2 lam 2 rho + constructedPhaseDamping 2 lam 4 rho) ∧
      depolarizing 2 (1 - lam) rho =
        ((((1+3*lam)/(4*(1+lam)) : ℝ) : ℂ)) •
          (constructedPhaseDamping 2 lam 2 rho + constructedPhaseDamping 2 lam 4 rho) +
        ((((1-lam)/(4*(1+lam)) : ℝ) : ℂ)) •
          (conjSuperop sz (constructedPhaseDamping 2 lam 2 rho) +
           conjSuperop sz (constructedPhaseDamping 2 lam 4 rho)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
