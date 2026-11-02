-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P31_transverse_heat_pole
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P31.transverse_heat_pole
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:41:31.525529+00:00
-- url     : https://prove2.me/theorems/e534d5bc-d60b-4dba-be1d-6519612143e3
-- title:
--   Transverse heat trace and its dimensional pole
-- statement:
--   For a real twist $\phi$ with $0<|\phi|\le\pi$, define
--
--   $$T_\phi(s)=\sum_{j\in\mathbb Z}e^{-s(2\pi j+\phi)^2},\qquad H(D,\phi)=\int_0^\infty T_\phi(s)^{D-2}\,ds.$$
--
--   The series converges for every $s>0$, and $H(D,\phi)$ converges for $2<D<4$. Its endpoint asymptotics are
--
--   $$\sqrt{4\pi s}\,T_\phi(s)\longrightarrow1\quad(s\downarrow0),\qquad e^{s\phi^2}T_\phi(s)\longrightarrow\begin{cases}1,&|\phi|<\pi,\2,&|\phi|=\pi\end{cases}\quad(s\to\infty).$$
--
--   There is a finite real number $F_\phi$ such that
--
--   $$\lim_{\epsilon\downarrow0}\left[H(4-\epsilon,\phi)-\frac1{2\pi\epsilon}\right]=F_\phi.$$
--
--   This is the analytic continuation and pole subtraction used in the transverse sum of (5.24). The twofold lowest-mode degeneracy supplies the endpoint correction at antiperiodic twist.
-- source:
--   Entanglement Entropy in the O(N) model, arXiv:0904.4477v1, PDF p. 30, §V C (5.25)–(5.29): analytic continuation of transverse sum

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P31

noncomputable section

open Filter Set MeasureTheory

open scoped Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P31

/-- PDF pp.29--30, (5.25)--(5.29): convergent heat continuation, endpoint
asymptotics, and the finite part after subtracting the MS pole. The unit
prefactor in printed (5.28) is for `|phi| < pi`; at `|phi| = pi` the two
lowest modes give the prefactor two. Zero twist is excluded. -/
theorem transverse_heat_pole (phi : ℝ) (hphi : 0 < |phi|)
    (hrep : |phi| ≤ Real.pi) :
    (∀ s : ℝ, 0 < s → Summable (transverseHeatTerm s phi)) ∧
    Tendsto (fun s : ℝ => Real.sqrt (4 * Real.pi * s) * transverseHeat s phi)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) ∧
    Tendsto (fun s : ℝ => Real.exp (s * phi ^ 2) * transverseHeat s phi)
      atTop (𝓝 (if |phi| = Real.pi then (2 : ℝ) else 1)) ∧
    (∀ D : ℝ, 2 < D → D < 4 →
      IntegrableOn (fun s : ℝ => (transverseHeat s phi) ^ (D - 2)) (Ioi 0)) ∧
    (∃ finitePart : ℝ,
      Tendsto (fun eps : ℝ => transverseIntegral (4 - eps) phi -
        1 / (2 * Real.pi * eps)) (𝓝[>] (0 : ℝ)) (𝓝 finitePart)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P31

end
