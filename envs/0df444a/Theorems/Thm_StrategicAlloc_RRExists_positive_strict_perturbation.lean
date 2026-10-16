-- Prove2me | Theorems.Thm_StrategicAlloc_RRExists_positive_strict_perturbation
-- name    : StrategicAlloc.RRExists.positive_strict_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:35:58.787929+00:00
-- url     : https://prove2.me/theorems/1f1eb5c1-f7c6-4fdf-b563-9f34f0c90650
-- title:
--   §A, p. 24, proof of Theorem A.3 — a positive strict perturbation within 2ε/3 on every bundle
-- statement:
--   Let $w : M \to \mathbb R_{\ge 0}$ be the values of one agent. Let $\varepsilon > 0$ be the smallest positive difference $|w(g) - w(h)|$ between the values of two goods (or $\varepsilon = 1$ if all goods have the same value), as in Lemma A.1, and let $\hat\varepsilon > 0$ be the smallest positive difference $|w(T) - w(T')|$ between the values of two bundles $T, T' \subseteq M$ (or $\hat\varepsilon = 1$ if all bundles have the same value). Then there is $w' : M \to \mathbb R$ such that
--
--   1. $w'(g) > 0$ for every good $g$;
--   2. $w'$ is injective (it induces a strict preference ranking);
--   3. $w'$ is consistent with $w$: $w(g) < w(h)$ implies $w'(g) < w'(h)$;
--   4. for every bundle $T \subseteq M$,
--   $$w(T) \le w'(T) \le w(T) + \frac{2\varepsilon}{3} \quad\text{and}\quad w'(T) \le w(T) + \frac{2\hat\varepsilon}{3}.$$
--
--   This is the first step of the proof of Theorem A.3: applied to each agent, it produces an instance to which Theorem A.2 applies, with every bundle value moved by less than the gap between distinct bundle values.
--
--   **Formalization Note** The page obtains $w'$ from Lemma A.1 with $\varepsilon$ the smallest positive difference between the values of two *goods* (`goodGap w`), then raises a single zero-valued good to $\varepsilon/3$; the first upper bound is the page's claim. The second upper bound, with the bundle-level gap $\hat\varepsilon$ = `bundleGap w`, is added (a disclosed strengthening): $\hat\varepsilon \le \varepsilon$ whenever $w$ takes two distinct values (singletons are bundles), and it is the form the next step of the proof needs (with values $0, 3, 5, 9$ the good-level gap is $2$ but the bundles $\{g_1,g_4\}$ and $\{g_2,g_3\}$ differ by $1$).
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 24, §A, proof of Theorem A.3, first paragraph (bundle-level ε: disclosed repair)

import Mathlib
import Definitions.Def_StrategicAlloc_RRExists_Setting

namespace StrategicAlloc.RRExists

/-- Proof of Theorem A.3, first paragraph (p. 24), with the bundle-level ε: every non-negative value
vector `w` has a positive, injective perturbation `w'` that preserves the strict order of `w` and
satisfies w(T) ≤ w'(T) ≤ w(T) + 2ε/3 for every bundle T, both for the page's good-level
ε = `goodGap w` (Lemma A.1) and for the bundle-level ε = `bundleGap w`. -/
theorem positive_strict_perturbation {m : ℕ} (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g) :
    ∃ w' : Fin m → ℝ, (∀ g, 0 < w' g) ∧ Function.Injective w' ∧
      (∀ g h, w g < w h → w' g < w' h) ∧
      ∀ T : Finset (Fin m), ∑ g ∈ T, w g ≤ ∑ g ∈ T, w' g ∧
        ∑ g ∈ T, w' g ≤ ∑ g ∈ T, w g + 2 * StrategicAlloc.RRFair.goodGap w / 3 ∧
        ∑ g ∈ T, w' g ≤ ∑ g ∈ T, w g + 2 * bundleGap w / 3 := by sorry

end StrategicAlloc.RRExists
