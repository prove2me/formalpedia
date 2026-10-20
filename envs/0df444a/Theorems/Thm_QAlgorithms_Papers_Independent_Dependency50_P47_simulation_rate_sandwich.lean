-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_simulation_rate_sandwich
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.simulation_rate_sandwich
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:37:00.282022+00:00
-- url     : https://prove2.me/theorems/caa82b33-b08e-4878-b729-89fb193e357a
-- title:
--   Theorem 2: entanglement-assisted simulation rate bounds
-- statement:
--   Fix a normalized finite law $p(a,b,x,y)$. Let $\mathcal R^q$ be the rates achievable by one-way classical communication from Alice to Bob, assisted by arbitrary finite shared entanglement independent of the i.i.d. inputs. Alice uses $X^n$ to produce $(A^n,M)$; Bob uses $(M,Y^n)$ to produce $B^n$. The message satisfies $H(M)\le nR$, and the unhalved $\ell_1$ error of the entire induced law relative to $p^{\otimes n}$ tends to zero.
--
--   For $\epsilon\ge0$, let $\mathcal S_\epsilon$ contain the real rates $R$ for which there exist a normalized approximate law $\widetilde p(a,b,x,y)$ and a finite cq extension
--   $\sum_{a,x,y}\widetilde p(a,x,y)|a,x,y\rangle\langle a,x,y|\otimes\rho_{a,x,y}^F$,
--   with $\|\widetilde p-p\|_1\le\epsilon$, $R\ge I(X;F\mid Y)$, $I(F;Y\mid X)=0$, and $I(A;Y\mid FX)=0$. A POVM on $F$ selected by $Y=y$ must induce the complete law $\widetilde p(a,b,x,y)$. Then
--
--   $$
--   \mathcal S_0\subseteq\mathcal R^q\subseteq\bigcap_{\epsilon>0}\mathcal S_\epsilon.
--   $$
--
--   This compares operational simulation rates with single-letter cq witnesses. The measurement is a channel to $B$, not a simultaneous joint register $BF$. Neither a quantum dimension cutoff nor an exact $XY$ marginal for positive error is imposed.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 8, Theorem 2: entanglement-assisted simulation rate bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Theorem 2, PDF p.8: the sandwich, with intersection over all positive errors.
No dimension cutoff, equality, closure, or extra fixed marginal is imposed. -/
theorem simulation_rate_sandwich {a b x y : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (p : Law (Fin a × Fin b × Fin x × Fin y)) :
    singleLetterRegion p 0 ⊆ quantumRates p ∧
      quantumRates p ⊆ {R | ∀ eps : ℝ, 0 < eps → R ∈ singleLetterRegion p eps} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
