-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P05_proposition1
-- name    : QAlgorithms.Papers.Independent.Frontier30.P05.proposition1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:11:26.499044+00:00
-- url     : https://prove2.me/theorems/cc2b76b3-3a98-48f5-a28f-d7399a4b8792
-- title:
--   Minimal entropy majorant and spectral asymptotics
-- statement:
--   Let $H$ be a positive self-adjoint Hamiltonian on its infinite-dimensional effective separable complex Hilbert space, with ordered eigenvalues $E_0\le E_1\le\cdots$ tending to infinity, counting multiplicities. Assume $(\operatorname{Tr}e^{-\lambda H})^\lambda\to1$ as $\lambda\downarrow0$. Let $F_H(E)$ be the supremum of the von Neumann entropies, in nats, of all density operators with mean energy at most $E$, and put $\bar F_H(x)=F_H(x+E_0)$. Define
--
--   $$
--   G_*(x)=\sqrt{x}\sup_{y\ge x}\frac{\bar F_H(y)}{\sqrt y}\quad(x>0),\qquad G_*(0)=\ln m(E_0),
--   $$
--
--   where $m(E_0)$ is the ground multiplicity. Then $G_*$ is continuous on $[0,\infty)$, majorizes $\bar F_H$ at positive arguments, satisfies $G_*(x)=o(\sqrt x)$, is strictly increasing on $(0,\infty)$, and $G_*(x)/\sqrt x$ is nonincreasing there. It is pointwise no larger than every other function with these properties, including at zero.
--
--   For ordered pairs of eigenvalue indices define $N_\uparrow(E)=\sum_{k,j:E_k+E_j\le E}E_k^2$ and $N_\downarrow(E)=\sum_{k,j:E_k+E_j\le E}E_kE_j$. If $N_\uparrow(E)/N_\downarrow(E)$ has a finite real limit $a>1$, there exists $E_*>0$ such that $\bar F_H(x)/\sqrt x$ is nonincreasing for $x\ge E_*$ and $G_*(x)=\bar F_H(x)$ throughout that range. Moreover,
--
--   $$
--   \lim_{x\to\infty}\frac{G_*(x)}{\ln x}=\frac1{a-1}.
--   $$
--
--   This identifies the minimal admissible entropy majorant and its precise logarithmic growth. The effective-space representation also covers a Hamiltonian whose domain is not dense in a larger ambient Hilbert space: every finite-energy state is supported in the effective space.
-- source:
--   Advanced Alicki-Fannes-Winter method for energy-constrained quantum systems and its use, arXiv:1907.02458v3, PDF p. 7, Proposition 1(A,B)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P05

noncomputable section

open Filter

open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Frontier30.P05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.7–8, Proposition 1(A,B). The majorant is admissible and pointwise
minimal on the entire nonnegative half-line. A finite spectral limit a>1
implies eventual monotonicity, eventual equality to the shifted ACTUAL
entropy capacity, and the full logarithmic asymptotic with coefficient 1/(a−1). -/
theorem proposition1 (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum)
    (h14 : Condition14 S) :
    (AdmissibleMajorant b S (minimalMajorant b S) ∧
      ∀ G : ℝ → ℝ, AdmissibleMajorant b S G →
        ∀ x : ℝ, 0 ≤ x → minimalMajorant b S x ≤ G x) ∧
    (∀ a : ℝ, SpectralRatioLimit S a →
      (∃ EStar : ℝ, 0 < EStar ∧
        AntitoneOn (fun x : ℝ => shiftedCapacity b S x / Real.sqrt x) (Set.Ici EStar) ∧
        ∀ x : ℝ, EStar ≤ x → minimalMajorant b S x = shiftedCapacity b S x) ∧
      Tendsto (fun x : ℝ => minimalMajorant b S x / Real.log x)
        atTop (nhds ((a - 1)⁻¹))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P05

end
