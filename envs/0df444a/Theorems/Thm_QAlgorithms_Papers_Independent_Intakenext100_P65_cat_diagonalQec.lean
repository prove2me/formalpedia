-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_cat_diagonalQec
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.cat_diagonalQec
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:27:37.353375+00:00
-- url     : https://prove2.me/theorems/337bcd16-0e7a-44a1-a14b-7457d9e8732c
-- title:
--   Exact cat diagonal QEC blocks and large-amplitude ratios
-- statement:
--   Fix integers $S,\ell\ge0$ and $0<\gamma<1$. For real $a>0$, use the normalized projected-coherent cat basis, and set $N_a^r=\langle a|\Pi_r|a\rangle$ with residues modulo $2(S+1)$. Put $P_\ell=e^{-\gamma a^2}(\gamma a^2)^\ell/\ell!$ and $R_\mu=N_{a\sqrt{1-\gamma}}^{(S+1)\mu-\ell}/N_a^{(S+1)\mu}$. The actual compressed block has entries
--
--   $$\langle\mu_a|E_\ell^\dagger E_\ell|
--   u_a\rangle=\delta_{\mu
--   u}P_\ell R_\mu,\qquad c_{\ell\ell}=\frac{P_\ell}{2}(R_0+R_1),\qquad z_{\ell\ell}=\frac{P_\ell}{2}(R_0-R_1).$$
--
--   For each logical label, $R_\mu\to1$ as $a\to\infty$. The comparison Poisson mean $\gamma a^2$ varies with amplitude, so this is not convergence to one fixed probability distribution.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 10, §V B (5.11)–(5.13): exact cat diagonal QEC blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.10--11 (5.11)--(5.13): exact diagonal blocks and their two coefficients;
the large-a assertion is about ratios, not a fixed limiting Poisson law. -/
theorem cat_diagonalQec (S : ℕ) (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (l : ℕ) :
    (∀ a > (0 : ℝ), qecBlock (catCodeCoordinates a S) g l l =
      fun i j => if i = j then ((poissonWeight a g l * catLossRatio a S g l i : ℝ) : ℂ) else 0) ∧
    (∀ a > (0 : ℝ),
      qecC (catCodeCoordinates a S) g l l = poissonWeight a g l *
        (catLossRatio a S g l 0 + catLossRatio a S g l 1) / 2 ∧
      qecZ (catCodeCoordinates a S) g l l = poissonWeight a g l *
        (catLossRatio a S g l 0 - catLossRatio a S g l 1) / 2) ∧
    (∀ mu : Fin 2, Tendsto (fun a => catLossRatio a S g l mu) atTop (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
