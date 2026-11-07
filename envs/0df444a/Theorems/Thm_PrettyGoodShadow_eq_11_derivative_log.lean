-- Prove2me | Theorems.Thm_PrettyGoodShadow_eq_11_derivative_log
-- name    : PrettyGoodShadow.eq_11_derivative_log
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:24:00.34419+00:00
-- url     : https://prove2.me/theorems/a6720341-fc8c-4472-bc4b-1fd048daf1a5
-- title:
--   Eq. (11) — $D_S$ is the derivative of the matrix logarithm at $S$
-- statement:
--   Let $S$ be positive semidefinite and let $H$ be Hermitian and supported on $\operatorname{supp}(S)$. Then
--
--   $$
--   \frac{d}{du}\log(S+uH)\Big|_{u=0}=D_S(H).
--   $$
--
--   This identity relates the outcome probabilities of the integral pretty good measurement to the logarithms in relative entropy, and it is the first step of Lemma 3.2.
--
--   **Formalization Note** The derivative is entrywise in the real variable $u$. The logarithm is functional calculus with $\log0=0$, that is, the logarithm on the support.
--
--   Differences from the source:
--   - generalization: S is the average state S(p, n) → S is any positive semidefinite operator; reason: the proof uses only that S is positive definite on its support, and S(p, n) is one such operator
--   - encoding: the page restricts to supp(S) and takes H Hermitian on that subspace → H is a Hermitian matrix on the whole space with Π H Π = H; reason: this is the same operator extended by 0; on supp(S) the operator S is positive definite, as in the proof on p.16
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), eq. (11), p.17

import Mathlib
import Definitions.Def_PrettyGoodShadow_divS

open scoped ComplexOrder

namespace PrettyGoodShadow

/-- **Eq. (11): `D_S` is the derivative of the matrix logarithm** (arXiv:2610.06781, sha256 bd055b7d…, p.17,
display on p.16). For `S` positive semidefinite and `H` Hermitian and supported on `supp(S)`,
`d/du log(S + uH)|_{u=0} = D_S(H)`.

**Formalization Note** The derivative is entrywise in the real variable `u`. The page restricts to `supp(S)`
before stating the identity; here `H` is supported on `supp(S)`, written `Π H Π = H`, and `log` is `cfc Real.log`,
which is `0` on the orthogonal complement of the support since `Real.log 0 = 0`. For `|u|` small, `S + uH` has
the same support as `S`. -/
theorem eq_11_derivative_log {ι : Type} [Fintype ι] [DecidableEq ι] (S H : Matrix ι ι ℂ)
    (hS : S.PosSemidef) (hH : H.IsHermitian) (hsupp : suppProj S * H * suppProj S = H) (a b : ι) :
    HasDerivAt (fun u : ℝ => (cfc Real.log (S + u • H)) a b) ((divS S H) a b) 0 := by sorry

end PrettyGoodShadow
