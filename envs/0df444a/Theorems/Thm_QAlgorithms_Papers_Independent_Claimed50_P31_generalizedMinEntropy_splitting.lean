-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P31_generalizedMinEntropy_splitting
-- name    : QAlgorithms.Papers.Independent.Claimed50.P31.generalizedMinEntropy_splitting
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:24:23.040994+00:00
-- url     : https://prove2.me/theorems/38a20424-4d05-485b-8c75-76e0c4b0f0cc
-- title:
--   Generalized min-entropy splitting with a law-defined choice bit
-- statement:
--   Let $\varepsilon\ge0$, let $\beta>0$ be real, and let $\alpha\in\mathbb R$ satisfy $\beta<\alpha$. Let $X_0,X_1,K,J$ have any joint discrete probability law on nonempty alphabets, where $J$ has the indexed alphabet $\{0,\ldots,d-1\}$ of cardinality $d=2^\beta$. Assume $H_{\min}^{\varepsilon}(X_0,X_1\mid K,J)\ge\alpha$, using the event-smoothed worst-case conditional entropy in bits. Define $f(x_0,x_1,k)=1$ if some $j$ satisfies $P_{X_1\mid K,J}(x_1\mid k,j)\ge2^{-(\alpha-\beta)/2}$, and define it to be zero otherwise. Unsupported conditioning values have conditional probability zero. Put $C=f(X_0,X_1,K)$. Then
--
--   $$H_{\min}^{\varepsilon}(X_{1-C},C\mid K,J)\ge\frac{\alpha-\beta}{2}.$$
--
--   The same prescribed choice rule applies to every actual value of $J$. The result provides a splitting rule when the distribution depends on an unknown bounded classical index.
--
--   **Formalization Note** Different alphabets for $X_0$ and $X_1$ are accommodated by a tagged union; the tag and $C$ encode the same joint random variable. The numbered lemma excludes $\beta=0$. The Lean cardinality parameter $d$ is a natural number with the explicit equality $d=2^\beta$; $\beta$ need not be integral.
-- source:
--   Composable Security in the Bounded-Quantum-Storage Model, arXiv:0709.0492v1, PDF p. 10, Lemma 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P31

open scoped ENNReal ComplexOrder

/-- Lemma 4.3, PDF pp.10-11. The choice is computed from the original
joint law and cannot depend on the actual value of J. The numbered lemma
assumes real beta>0 and an index alphabet of cardinality 2^beta.
The cardinality equality does not require beta to be an integer; beta=0 is not added. -/
theorem generalizedMinEntropy_splitting
    (Omega A0 A1 K : Type*) [Nonempty Omega] [Nonempty A0] [Nonempty A1] [Nonempty K]
    (p : PMF Omega) (X0 : Omega → A0) (X1 : Omega → A1) (Kvar : Omega → K)
    (jCount : ℕ) (J : Omega → Fin jCount) (alpha beta epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hbeta : 0 < beta) (hbetaAlpha : beta < alpha)
    (hcard : (jCount : ℝ) = Real.rpow 2 beta)
    (hentropy : (alpha : EReal) ≤ eventSmoothMinEntropy p
      (fun w => (X0 w, X1 w)) (fun w => (Kvar w, J w)) epsilon) :
    (((alpha - beta) / 2 : ℝ) : EReal) ≤ eventSmoothMinEntropy p
      (splittingOutput p X0 X1 Kvar J alpha beta) (fun w => (Kvar w, J w)) epsilon := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P31

end
