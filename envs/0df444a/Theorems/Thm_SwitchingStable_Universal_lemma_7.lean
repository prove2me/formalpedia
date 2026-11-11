-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_7
-- name    : SwitchingStable.Universal.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:21.396963+00:00
-- url     : https://prove2.me/theorems/f9f0dc93-e96e-46b5-ba7d-549e813182ac
-- title:
--   Lemma 7 — Stable next-owner cycle swaps
-- statement:
--   Work in the promoted strict market, fix a stable matching $\mu$ and either direction, and let distinct active men $a_0,\ldots,a_{k-1}$ form a directed next-owner cycle, with $k\ge2$. Reassign their partners cyclically and keep every other edge. The resulting matching $\nu$ is stable and satisfies
--   $$\nu(a_i)=\mu(a_{i+1}),\qquad\varepsilon\bigl(\operatorname{idx}_{a_i}(\nu)-\operatorname{idx}_{a_i}(\mu)\bigr)=1.$$
--   Indices of the cycle are modulo $k$. Both improving and worsening swaps, including their exact one-position movement, are retained.
--
--   Differences from the source:
--   - encoding: From Lemma 6 onward every agent ranks all stable partners first → The stable-partners-first property is explicit; the cycle is an injective map from Fin k; reason: This is the section standing assumption; such a market is itself its promoted market, so no permitted market is lost.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 5, PDF p. 6, Lemma 7

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_7 {n k : ℕ} (I : StableMatching.Instance n) (hI : StablePartnersFirst I)
    (μ : StableMatching.Matching n) (hμ : I.IsStable μ) (ε : Direction)
    (hk : 2 ≤ k) (a : Fin k → Fin n) (ha : Function.Injective a)
    (hactive : ∀ j, Active I μ ε (a j))
    (hcycle : ∀ j : Fin k, next I μ ε (a j) = a ⟨(j.val+1)%k, Nat.mod_lt _ (by omega)⟩) :
    ∃ ν : StableMatching.Matching n, I.IsStable ν ∧
      (∀ j : Fin k, ν (a j) = μ (a ⟨(j.val+1)%k, Nat.mod_lt _ (by omega)⟩)) ∧
      (∀ u : Fin n, u ∉ Set.range a → ν u = μ u) ∧
      (∀ j : Fin k, ε.sign * ((idx I ν (a j) : ℤ) - (idx I μ (a j) : ℤ)) = 1) := by sorry

end SwitchingStable.Universal
