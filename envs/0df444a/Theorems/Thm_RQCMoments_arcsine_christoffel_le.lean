-- Prove2me | Theorems.Thm_RQCMoments_arcsine_christoffel_le
-- name    : RQCMoments.arcsine_christoffel_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:47.665732+00:00
-- url     : https://prove2.me/theorems/1b85a746-834f-4125-8234-6ceef49eea87
-- title:
--   Lemma 4.3 proof, (61)/(65) — $\lambda_{\rho_R,\ell}(u)\le 4/\ell$ on $[0,R]$
-- statement:
--   For $R>0$ let $\rho_R$ be the arcsine probability measure on $[0,R]$, $d\rho_R(t)=dt/(\pi\sqrt{t(R-t)})$. For every integer $\ell\ge 1$ and every $u\in[0,R]$,
--   $$
--   \lambda_{\rho_R,\ell}(u)\le\frac{4}{\ell}.
--   $$
--
--   Theorem 4.4 (Step 1) uses the case $R=1$: "the Chebyshev polynomial construction in the proof of Lemma 4.3, specifically (65), shows that $\lambda_{\rho_1,\ell}(x)\le 4/\ell$ for $x\in[0,1]$. This also holds for $\ell=1$"; the proof of Lemma 4.3 uses $R=8\ell$.
--
--   Differences from the source:
--
--   - generalization: R = 1 (Theorem 4.4, Step 1) → every R > 0; reason: the proof of Lemma 4.3 establishes (61) and (65) for every R > 0 and u ∈ [0, R]; R = 1 is an instance
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), proof of Lemma 4.3, (61) and (65), p.23 (PDF p.25); Theorem 4.4, Step 1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_RQCMoments_christoffel
import Definitions.Def_RQCMoments_arcsine

set_option autoImplicit false

namespace RQCMoments

/-- **Arcsine Christoffel bound** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), proof of Lemma 4.3, (61) and (65), p.23, PDF p.25;
Theorem 4.4, Step 1, p.25, PDF p.27).
For every `R > 0`, every integer `ℓ ≥ 1` and every `u ∈ [0, R]`, the Christoffel function of the
arcsine measure `ρ_R` satisfies `λ_{ρ_R,ℓ}(u) ≤ 4/ℓ`.

**Formalization Note** The paper states the bound for `ρ₁` in Theorem 4.4 (Step 1) and proves it
for every `R > 0` in the proof of Lemma 4.3; the statement here is for every `R > 0`. -/
theorem arcsine_christoffel_le (R : ℝ) (hR : 0 < R) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (u : ℝ)
    (hu : u ∈ Set.Icc 0 R) :
    christoffel (arcsine R) ℓ u ≤ 4 / ℓ := by sorry

end RQCMoments
