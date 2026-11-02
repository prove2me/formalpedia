-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_rank3_gaussian_rounding_distribution
-- name    : QuantumMaxCutEnergy.rank3_gaussian_rounding_distribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-01T23:03:49.399792+00:00
-- url     : https://prove2.me/theorems/3e50baee-5883-4404-981c-e6b9103c1782
-- title:
--   Law of the rank-three Gaussian rounding has pair means $0.046+0.954\,X_{ij}$ (BOV 2014, Lemma 2.1)
-- statement:
--   **Rank-three Gaussian rounding distribution.**
--
--   Let $X$ be a real positive semidefinite matrix of order $n$ with $X_{ii}=1$, i.e. a feasible point of the Max-Cut semidefinite relaxation, and let $r_i\in\mathbb R^3$ denote the Bloch vector attached to vertex $i$.
--
--   Then there is a probability measure $\mu$ on the space $(\mathbb R^3)^n$ of Bloch assignments, supported on unit vectors, whose pair correlations are bounded in mean by $0.046+0.954\,X_{ij}$:
--
--   $$\mu\Big(\big\{r : \forall i,\ \lVert r_i\rVert=1\big\}\Big)=1,
--   \qquad
--   \int \Big(\sum_{a=1}^{3} r_{ia}r_{ja}\Big)\,d\mu(r)\;\le\;0.046+0.954\,X_{ij}
--   \quad\text{for all } i,j.$$
--
--   The measure is the law of the rank-three Gaussian rounding: take a Gram factor $X=UU^{\mathsf T}$, let $G$ be a $3\times n$ matrix of independent standard Gaussians and set
--   $$r_i=\frac{GU_i}{\lVert GU_i\rVert},\qquad i=1,\dots,n .$$
--   Because the rows of $G$ are independent, the pair $(GU_i,GU_j)$ has the law of $(Z,cZ+sZ')$ with $c=X_{ij}$, $s=\sqrt{1-c^{2}}$ and $Z,Z'$ independent standard Gaussians on $\mathbb R^3$; hence $\mathbb E\langle r_i,r_j\rangle$ depends on $X$ only through $X_{ij}$, and it equals the Briët–de Oliveira Filho–Vallentin series
--   $$f(c)=\sum_{k\ge 0}\alpha_k c^{2k+1},\qquad \alpha_k=\frac{24\,(5/2)_k}{\pi\,k!\,(2k+1)^{2}(2k+3)^{2}}\ \ge 0,\qquad \sum_{k}\alpha_k=1,$$
--   whose first two coefficients are $\alpha_0=8/(3\pi)$ and $\alpha_1=4/(15\pi)$. The scalar certificate $\alpha_k\ge0$, $\sum_k\alpha_k=1$, $\alpha_1\ge 14/165$, $\alpha_0\ge 28/33$ gives $f(c)\le 0.046+0.954\,c$ on $[-1,1]$, with equality at $c=1$; that is the content of the platform theorem `QuantumMaxCutEnergy.rank3_odd_series_ratio_0954`. This statement isolates exactly the existence of the joint distribution with those first moments — the probabilistic core of the rounding argument, stripped of the final averaging step (which is proved separately).
-- source:
--   Briet, de Oliveira Filho and Vallentin, Theory of Computing 10(4), 2014, Lemma 2.1 (the matrix Grothendieck identity behind rank-three rounding), https://doi.org/10.4086/toc.2014.v010a004 ; Anshu, Gosset and Morenz, TQC 2020, Theorem 1, https://doi.org/10.4230/LIPIcs.TQC.2020.7 ; scalar certificate as in Gharibian and Parekh, APPROX/RANDOM 2019, Appendix C Lemma 10 (platform theorem QuantumMaxCutEnergy.rank3_odd_series_ratio_0954).

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators
open MeasureTheory

theorem QuantumMaxCutEnergy.rank3_gaussian_rounding_distribution
    (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    ∃ μ : MeasureTheory.Measure (Fin n → Fin 3 → ℝ),
      MeasureTheory.IsProbabilityMeasure μ ∧
        (∀ᵐ r ∂μ, ∀ i : Fin n, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
          ∀ i j : Fin n,
            ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ ≤ 0.046 + 0.954 * X i j := by sorry
