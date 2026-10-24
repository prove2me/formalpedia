-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_remark_6_2
-- name    : QAlgorithms.Papers.Independent.Support50.P12.remark_6_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:42:13.080663+00:00
-- url     : https://prove2.me/theorems/cd941121-0e76-40d2-863e-f4de40a5c174
-- title:
--   Remark 6.2
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   Put $\widetilde\psi(s)=(1+s)\psi(s/(1+s))$ for $s\ge0$ and $+\infty$ for $s<0$, and $h^*(r)=\sup_s\{sr-h(s)\}$. Then $H_r=\widetilde\psi^*(-r)$ is convex and decreasing in $r$, $\psi(0)=-S_0(A\Vert B)$, $\psi(1)=-S_0(B\Vert A)$, and
--
--   $$-S_\alpha(A\Vert B)=\sup_{r\in\mathbb R}\left\{-\frac{r\alpha}{1-\alpha}-H_r(A\Vert B)\right\},\quad0\le\alpha<1.$$
--
--   For nonorthogonal pairs, $\psi$ is real convex and $\widetilde\psi$ is lower semicontinuous and convex. Its derivative is $\psi(s/(1+s))+\psi\prime(s/(1+s))/(1+s)$, its right derivative at zero is $\psi(0)+\psi\prime(0)$, and its derivative tends to $\psi(1)$ at infinity. If $-r<\psi(0)+\psi\prime(0)$, $H_r=-\psi(0)$; if $-r>\psi(1)$, $H_r=+\infty$. Bipolarity holds on $s\ge0$, and the displayed supremum can be restricted to the closed interval $[-\psi(1),-\psi(0)-\psi\prime(0)]$, including a singleton. If $\operatorname{Tr}A\le1$, $S_\alpha$ increases on $[0,1)$, $\lim_{\alpha\uparrow1}S_\alpha=H_0=:S_1$, and $\lim_{r\downarrow0}H_r=H_0$. When $\operatorname{Tr}A=1$, $S_1=S(A\Vert B)$. No derivative is assigned to the identically $-\infty$ orthogonal case. These identities relate the Rényi and Hoeffding families.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 27, Remark 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Remark 6.2, PDF pp.27–28: polar duality, restricted CLOSED interval, derivatives
on nonorthogonal pairs, and the trace-guarded order-one and right-rate limits.
The separately deferred unnormalized endpoint-entropy derivative formulas are omitted. -/
theorem remark_6_2 [Nonempty I] (X Y : Mat I) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∀ r : ℝ, hoeffding X Y r = polar (logOverlapPerspective X Y) (-r)) ∧
    (∀ r s : ℝ, r ≤ s → hoeffding X Y s ≤ hoeffding X Y r) ∧
    ExtendedConvex (hoeffding X Y) ∧
    logOverlap X Y 0 = -petzRenyi 0 X Y ∧ logOverlap X Y 1 = -petzRenyi 0 Y X ∧
    (∀ a ∈ Ico (0 : ℝ) 1, -petzRenyi a X Y =
      sSup {v | ∃ r : ℝ, v = ((-r * a / (1 - a) : ℝ) : EReal) - hoeffding X Y r}) ∧
    (0 < tr (supp X * supp Y) →
      ConvexOn ℝ univ (psiReal X Y) ∧ ExtendedConvex (logOverlapPerspective X Y) ∧
      LowerSemicontinuous (logOverlapPerspective X Y) ∧
      (∀ s > 0, HasDerivAt (fun u => (logOverlapPerspective X Y u).toReal)
        (psiReal X Y (s / (1 + s)) + deriv (psiReal X Y) (s / (1 + s)) / (1 + s)) s) ∧
      HasDerivWithinAt (fun u => (logOverlapPerspective X Y u).toReal)
        (psiReal X Y 0 + deriv (psiReal X Y) 0) (Ici 0) 0 ∧
      Tendsto (fun s : ℝ => deriv (fun u => (logOverlapPerspective X Y u).toReal) s)
        atTop (𝓝 (psiReal X Y 1)) ∧
      (∀ r : ℝ, -r < psiReal X Y 0 + deriv (psiReal X Y) 0 →
        hoeffding X Y r = -logOverlap X Y 0) ∧
      (∀ r : ℝ, psiReal X Y 1 < -r → hoeffding X Y r = ⊤) ∧
      (∀ s ≥ 0, logOverlapPerspective X Y s = polar (polar (logOverlapPerspective X Y)) s) ∧
      (∀ a ∈ Ico (0 : ℝ) 1, -petzRenyi a X Y =
        sSup {v | ∃ r : ℝ, -psiReal X Y 1 ≤ r ∧
          r ≤ -psiReal X Y 0 - deriv (psiReal X Y) 0 ∧
          v = ((-r * a / (1 - a) : ℝ) : EReal) - hoeffding X Y r})) ∧
    (tr X ≤ 1 →
      MonotoneOn (fun a => petzRenyi a X Y) (Ico 0 1) ∧
      Tendsto (fun a => petzRenyi a X Y) (𝓝[<] 1) (𝓝 (hoeffding X Y 0)) ∧
      Tendsto (hoeffding X Y) (𝓝[>] 0) (𝓝 (hoeffding X Y 0)) ∧
      hoeffding X Y 0 = renyiOne X Y) ∧
    (tr X = 1 → renyiOne X Y = relativeEntropy X Y) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
