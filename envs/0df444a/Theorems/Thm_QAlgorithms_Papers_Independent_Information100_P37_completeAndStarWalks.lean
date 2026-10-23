-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_completeAndStarWalks
-- name    : QAlgorithms.Papers.Independent.Information100.P37.completeAndStarWalks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:22:24.077995+00:00
-- url     : https://prove2.me/theorems/6c18802c-a76a-46c9-9ddc-a42d3b0573a9
-- title:
--   Appendix D, Eqs. (D1)–(D5): complete and star walks
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $d\ge2$, $J_d$ be the all-ones matrix, and $\Pi_d=J_d/d$. For complete adjacency $J_d-I$, spectral normalization gives $H_K=(J_d-I)/(d-1)$ and
--   $$U_K(t)=e^{-it}\Pi_d+e^{it/(d-1)}(I-\Pi_d),\quad P_K(t)=\Pi_d+r_d(t)(I-\Pi_d),$$
--   $$r_d(t)=\frac{d-2+2\cos(dt/(d-1))}{d}.$$
--   For the star with hub $0$, put $|s\rangle=(d-1)^{-1/2}\sum_{j=1}^{d-1}|j\rangle$. Its spectrally normalized Hamiltonian is $H_S=|0\rangle\langle s|+|s\rangle\langle0|$, and
--   $$G_{U_S(\pi)}=\frac{8(d-3)}{(d-1)^2}(0\oplus H_{d-1}).$$
--   The subtraction $d-3$ is real; at $d=2$ the leaf projector vanishes, and at $d=3$ the coefficient vanishes.
--
--   These exact graph-walk formulas supply the topology comparison and preserve its low-dimensional limits.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 14, Appendix D, Eqs. (D1)–(D5): complete and star walks

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.14, Appendix D, (D1)--(D5): complete and star walks, including d=2,3. -/
theorem completeAndStarWalks (d : ℕ) (hd : 2 ≤ d) :
    (specNorm (completeAdjacency d))⁻¹ • completeAdjacency d =
      (((d : ℂ) - 1)⁻¹) • completeAdjacency d ∧
    (∀ t : ℝ,
      walk (completeAdjacency d) t =
        Complex.exp (-Complex.I * (t : ℂ)) • (uniformProjector d).map Complex.ofReal +
        Complex.exp (Complex.I * (t : ℂ) / ((d : ℂ) - 1)) •
          (1 - (uniformProjector d).map Complex.ofReal) ∧
      transition (walk (completeAdjacency d) t) = uniformProjector d +
        ((((d : ℝ) - 2) + 2 * Real.cos (d * t / ((d : ℝ) - 1))) / d) •
          (1 - uniformProjector d)) ∧
    (specNorm (starAdjacency d))⁻¹ • starAdjacency d =
      (fun i j => (if i.val = 0 then conj (leafState d j) else 0) +
        (if j.val = 0 then leafState d i else 0)) ∧
    response (walk (starAdjacency d) Real.pi) =
      (8 * ((d : ℝ) - 3) / ((d : ℝ) - 1) ^ 2) • leafProjector d := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
