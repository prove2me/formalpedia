-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P05_multipleGenerators_rieszCriterion
-- name    : QAlgorithms.Papers.Independent.Renew46.P05.multipleGenerators_rieszCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:00:35.752238+00:00
-- url     : https://prove2.me/theorems/0400b5d0-01d8-4323-bf4c-d42533a21ad5
-- title:
--   §2.4, unnumbered: Riesz criterion for multiple translated HS generators
-- statement:
--   Let $d\ge1$ and let $\mathcal H=L^2(\mathbb R^d;\mathbb C)$ with Lebesgue measure. Write $\mathrm{HS}(\mathcal H)$ for the Hilbert–Schmidt operators, with first-linear pairing $\langle T,Q\rangle_{\mathrm{HS}}=\operatorname{tr}(TQ^*)$. Let $\Lambda=A\mathbb Z^{2d}$ be a full-rank phase-space lattice, and set $\alpha_z(T)=\pi(z)T\pi(z)^*$, where $\pi(x,\omega)f(t)=e^{2\pi i\omega\cdot t}f(t-x)$. Lattice Fourier series use $e^{2\pi i\sigma(\lambda,z)}$, where $\sigma((x,\omega),(x',\omega'))=\omega\cdot x'-\omega'\cdot x$, and normalized Haar measure on $\widehat\Lambda$.
--
--   Let $N\ge1$ and let $S_1,\ldots,S_N$ be arbitrary HS operators; their translates are not assumed Riesz. Let $a_{S_n}$ be the actual Weyl symbols, defined by the weak cross-Wigner pairing. The continuous $L^2$ symplectic Fourier transform has kernel $e^{-2\pi i\sigma(z,z')}$. For the adjoint lattice $\Lambda^\circ$, define the Gram matrix, without a covolume prefactor, by
--   $$
--   G_{\mathbf S}^{\sigma}(z)_{nn'}
--   =\sum_{\lambda^\circ\in\Lambda^\circ}
--   \mathcal F_\sigma a_{S_n}(z+\lambda^\circ)\,
--   \overline{\mathcal F_\sigma a_{S_{n'}}(z+\lambda^\circ)}.
--   $$
--   Then $(\alpha_\lambda(S_n))_{n,\lambda}$ is a Riesz sequence if and only if there are constants $0<a\le b<\infty$ with
--   $$
--   a\|v\|_2^2\le v^*G_{\mathbf S}^{\sigma}(z)v\le b\|v\|_2^2
--   \quad\text{for almost every }z\text{ and every }v\in\mathbb C^N.
--   $$
--
--   If every $S_n$ belongs to $\mathcal B$, meaning its Weyl symbol lies in the Feichtinger algebra $S_0$, the same equivalence holds pointwise for every $z$ with $G_{\mathbf S}^{W}$ in place of $G_{\mathbf S}^{\sigma}$. This matrix is defined by the same periodization using
--   $$
--   \mathcal F_W(S)(x,\omega)
--   =e^{-\pi i x\cdot\omega}\operatorname{tr}[\pi(-x,-\omega)S].
--   $$
--   Here $S_0$ is defined by integrability of the Gaussian-window short-time Fourier transform. The class $\mathcal B$ supplies trace-class operators and continuous Fourier-Wigner representatives. All bounds use constants uniform in $z$ and $v$.
--
--   This is the operator-space application of the classical symbol criterion attributed by the source to reference [1], together with its regular pointwise refinement.
-- source:
--   Average sampling in certain subspaces of Hilbert-Schmidt operators on $L^2(\mathbb{R}^d)$, arXiv:2011.05871v2, PDF p. 6, §2.4, unnumbered: Riesz criterion for multiple translated HS generators

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P05

open Filter MeasureTheory

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Next46.P31 (EuclideanSchrodinger PhasePoint)

open QAlgorithms.Papers.Independent.Next46.P02 (hilbertSchmidtNorm)

open scoped BigOperators ENNReal Topology ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P05.unitCircleMeasureSpace

/-- García, PDF pp.6–7, Section 2.4: the operator-valued multigenerator
criterion, with the general a.e. Fourier-symbol condition and the pointwise
Fourier-Wigner refinement ONLY for B generators. The Riesz property is not
assumed. The classical symbol criterion is expressly attributed to [1]. -/
theorem multipleGenerators_rieszCriterion {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (L : Lattice d) (S : Fin N → SchrodingerOperator d) (hS : ∀ n, IsHS (S n)) :
    (IsHSRieszSequence (translatedGenerators L S) ↔
      ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
        ∀ᵐ z ∂(volume : Measure (SymbolCoordinate d)), GramBounds (symbolGram L S z) a b) ∧
    ((∀ n, InOperatorB (S n)) →
      (IsHSRieszSequence (translatedGenerators L S) ↔
        ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
          ∀ z : SymbolCoordinate d, GramBounds (wignerGram L S z) a b)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P05

end
