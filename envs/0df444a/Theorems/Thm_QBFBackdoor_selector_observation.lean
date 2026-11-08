-- Prove2me | Theorems.Thm_QBFBackdoor_selector_observation
-- name    : QBFBackdoor.selector_observation
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:31:29.852766+00:00
-- url     : https://prove2.me/theorems/6408d826-843b-4661-a0ed-4fe444c642b8
-- title:
--   Proof of Lemma 5.7 — the selector observation $\exists Z\forall W.\bigvee_{s\in T}E_s\iff|T|\ge 2^p$
-- statement:
--   Let $k,p\ge0$, let $Z=\{z_{s,\ell}: s\in[k],\ \ell\in[p]\}$ and $W=\{w_1,\dots,w_p\}$ be Boolean variables, and let
--
--   $$
--   E_s=\bigwedge_{\ell=1}^{p}(z_{s,\ell}=w_\ell)\qquad(s\in[k]).
--   $$
--
--   Then for every set $T\subseteq[k]$,
--
--   $$
--   \exists Z\,\forall W.\ \bigvee_{s\in T}E_s \iff |T|\ge 2^p .
--   $$
--
--   Each tuple $(z_{s,1},\dots,z_{s,p})$ matches one of the $2^p$ assignments to $W$. In Lemma 5.7, $T$ is the set of indices $s$ whose part $A_s$ is satisfied, and the observation converts "at least $2^p$ satisfied parts" into a quantified condition.
--
--   Differences from the source:
--   - generalization: k, p positive (the setting of Lemma 5.7) and T = {s : As is satisfied} → all k, p ≥ 0 and every T ⊆ [k]; reason: the observation does not use how T arises; the case of Lemma 5.7 is a special case
--   - encoding: Es = ⋀ℓ (zs,ℓ = wℓ) → the tuple z s equals w (as functions Fin p → Bool); reason: the same condition
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Lemma 5.7, p.25

import Mathlib

namespace QBFBackdoor

/-- **The selector observation.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Lemma 5.7, p.25: "We first make the following
selector observation: for any fixed assignment to Y, writing T = {s : As is satisfied}, we have
∃Z∀W. ⋁_{s∈T} Es ⇐⇒ |T| ≥ r." Here (p.24) `Z = {z_{s,ℓ} : s ∈ [k], ℓ ∈ [p]}`,
`W = {w₁, …, w_p}`, `E_s = ⋀_{ℓ=1}^p (z_{s,ℓ} = w_ℓ)` and `r = 2^p`.

For every set `T` of indices `s ∈ [k]`: there are values `z_{s,ℓ}` such that every assignment
`w` to `W` agrees with the tuple `(z_{s,1}, …, z_{s,p})` of some `s ∈ T` iff `|T| ≥ 2^p`.

**Formalization Note** `[k]` is `Fin k` and `[p]` is `Fin p`; `E_s` holds exactly when the
tuple `z s` equals `w`. Stated for all `k, p ≥ 0`; Lemma 5.7 uses `k, p ≥ 1`. -/
theorem selector_observation (k p : ℕ) (T : Finset (Fin k)) :
    (∃ z : Fin k → Fin p → Bool, ∀ w : Fin p → Bool, ∃ s ∈ T, z s = w) ↔ 2 ^ p ≤ T.card := by sorry

end QBFBackdoor
