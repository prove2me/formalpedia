-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_lemma_3_4
-- name    : QMomentMatch.FirstBound.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:59:48.02185+00:00
-- url     : https://prove2.me/theorems/c6fe35f1-80e0-4eba-aebc-77b93ad73120
-- title:
--   Lemma 3.4 — moment cancellation, in the monomial and binomial bases
-- statement:
--   Let $A,r\ge1$ be integers and let $\pi,\nu$ be probability distributions on $\{0\}\cup[A]$ with matching moments through order $r-1$:
--   $$\sum_{s=0}^A\nu(s)s^k=\sum_{s=0}^A\pi(s)s^k\qquad(k=1,\dots,r-1).$$
--   Let $\phi_\ell$ be either the monomial basis $\phi_\ell(z)=z^\ell$ or the binomial basis $\phi_\ell(z)=\binom z\ell$, $\ell\ge0$. Suppose $q(s)=\sum_{\ell=0}^D a_\ell\phi_\ell(s)$ on $\{0\}\cup[A]$ for an integer $D\ge0$. Then
--   $$\sum_{s=0}^A(\nu(s)-\pi(s))q(s)=\sum_{\ell=r}^D\eta_\ell a_\ell,\qquad\text{where }\eta_\ell=\sum_{s=0}^A(\nu(s)-\pi(s))\phi_\ell(s),$$
--   and $|\eta_\ell|\le\|\nu-\pi\|_1\,\phi_\ell(A)$ for every $\ell\ge0$, with $\|\nu-\pi\|_1=\sum_s|\nu(s)-\pi(s)|$.
--
--   Matching moments cancel the low-order part of any polynomial test function; the remaining terms are controlled by the high-order coefficients.
--
--   Differences from the source:
--   - encoding: "choose one of the two bases" → a hypothesis that $\phi$ equals the monomial basis or the binomial basis, with $\phi_\ell$ evaluated at natural numbers; reason: both bases are covered, and $\phi_\ell$ is only evaluated at $s\in\{0,\dots,A\}$.
--   - encoding: $\{0\}\cup[A]$ → `Fin (A + 1)`; reason: index convention.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 3.4, pp. 16–17

import Mathlib
import Definitions.Def_QMomentMatch_FirstBound_Basic

namespace QMomentMatch.FirstBound

/-- Lemma 3.4 (Moment cancellation), pp. 16–17, for both bases `ϕ_ℓ(z) = z^ℓ` and
`ϕ_ℓ(z) = (z choose ℓ)`. -/
theorem lemma_3_4 (A r : ℕ) (hA : 1 ≤ A) (hr : 1 ≤ r) (π ν : Fin (A + 1) → ℝ)
    (hπ : IsProbVec π) (hν : IsProbVec ν)
    (hmom : ∀ k : ℕ, 1 ≤ k → k ≤ r - 1 → moment ν k = moment π k)
    (φ : ℕ → ℕ → ℝ)
    (hφ : φ = (fun ℓ s : ℕ => (s : ℝ) ^ ℓ) ∨ φ = (fun ℓ s : ℕ => ((s.choose ℓ : ℕ) : ℝ)))
    (D : ℕ) (a : ℕ → ℝ) (q : Fin (A + 1) → ℝ)
    (hq : ∀ s : Fin (A + 1), q s = ∑ ℓ ∈ Finset.range (D + 1), a ℓ * φ ℓ s) :
    ∑ s, (ν s - π s) * q s =
        ∑ ℓ ∈ Finset.Icc r D, (∑ s : Fin (A + 1), (ν s - π s) * φ ℓ s) * a ℓ ∧
      ∀ ℓ : ℕ, |∑ s : Fin (A + 1), (ν s - π s) * φ ℓ s| ≤ (∑ s, |ν s - π s|) * φ ℓ A := by sorry

end QMomentMatch.FirstBound
