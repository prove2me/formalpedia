-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_cumulant_le_integral_const
-- name    : TFIMPhaseDiagram.Classical.Supplement.cumulant_le_integral_const
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T06:17:49.940804+00:00
-- url     : https://prove2.me/theorems/447243ae-667d-4cb0-ab93-0c11af71cbaa
-- title:
--   Reflection-positivity bound $\Lambda_\eta(h)\le\int_0^1\Lambda_\eta(h(t)\mathbf 1)\,dt$
-- statement:
--   This is the reflection-positivity bound of Chayes, Crawford, Ioffe and Levit for the path-space cumulant of the transverse-field (quantum Curie–Weiss) loop measure, at inverse temperature $\beta=1$.
--
--   Let $\eta>0$ and let $\nu_\eta$ be the zero-parity path law on the unit circle $S=[0,1)$. Under $\nu_\eta$, a $\pm1$-valued loop $\sigma$ flips at the points of a rate-$\eta$ Poisson process conditioned to have an even number of points, and its initial value is uniform. Viewed in $L^2(S)$, it gives the cumulant
--
--   $$\Lambda_\eta(h)=\log\mathbb E_{\sigma\sim\nu_\eta}\big[e^{\langle h,\sigma\rangle}\big],\qquad h\in L^2(S).$$
--
--   Then, for every $h\in L^2(S)$,
--
--   $$\Lambda_\eta(h)\le\int_0^1\Lambda_\eta\big(h(t)\cdot\mathbf 1\big)\,dt ,$$
--
--   where $c\cdot\mathbf 1$ is the constant function. Explicitly, $\Lambda_\eta(c\mathbf 1)=\log\frac{\cosh\sqrt{\eta^2+c^2}}{\cosh\eta}$.
--
--   The bound reduces variational problems over arbitrary fields $h$ to constant fields. It is the step used in the proof of Lemma 27 of the TFIM phase-diagram paper to compare $\Phi_{b,\eta}(bq)$ with the integral of the scalar free energy along $q$.
--
--   **Formalization Note** $\Lambda_\eta$ is `cumulant η`, the law $\nu_\eta$ is the push-forward `nuL2 η` of `pathLaw η false`, the constant function is `constL2`, and $dt$ is `circleVolume`, Lebesgue measure on $[0,1)$.
-- source:
--   L. Chayes, N. Crawford, D. Ioffe, A. Levit, The Phase Diagram of the Quantum Curie-Weiss Model, J. Stat. Phys. 133 (2008) 131-149, https://arxiv.org/abs/0804.1605, p. 11, Lemma 5.2, Eq. (5.7) with beta = 1; cited as [18, Lemma 5.2, Eq. (5.7)] in the proof of Lemma 27 (p. 17) of 'A computational phase diagram for the transverse field Ising model' (arXiv:2610.02079).

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_pathSpace
open MeasureTheory

namespace TFIMPhaseDiagram.Classical.Supplement
theorem cumulant_le_integral_const (η : ℝ) (hη : 0 < η) (h : CircleL2) :
    cumulant η h ≤ ∫ t, cumulant η (constL2 (h t)) ∂circleVolume := by sorry
end TFIMPhaseDiagram.Classical.Supplement
