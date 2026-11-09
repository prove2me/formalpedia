-- Prove2me | Theorems.Thm_RandomQueryXOR_observation_4_3
-- name    : RandomQueryXOR.observation_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:05:21.504368+00:00
-- url     : https://prove2.me/theorems/47ab128f-8c1a-4551-bc98-cf06c88ec27f
-- title:
--   Observation 4.3 — $\mathcal D_{f\oplus}$ fixes $g_{f\oplus}$; flipping a planted bit flips it
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$, $x^\star\in\{0,1\}^n$, $g=f\circ\oplus_2$, and let $y$ lie in the support of $\mathcal D_{f\oplus}$. Then $g(y)=f(x^\star)$, and for every sensitive bit $i$ of $x^\star$ with $x^\star(i)=0$,
--   $$
--   g(y\oplus e_{2i})=g(y\oplus e_{2i-1})=\neg f(x^\star).
--   $$
--
--   The observation is what makes $\mathcal D_{f\oplus}$ a hard distribution: the value of $g$ is fixed on it, but a single change in any planted pair changes the answer, and the embedding protocol plants the two-bit game in such a pair.
--
--   Differences from the source:
--   - generalization: x⋆_f a maximum-sensitivity input (Assumption 4.2) → any x⋆ ∈ {0,1}^n; reason: the observation does not use maximality; it specializes to x⋆_f
--   - encoding: y ∼ D_{f⊕} → y with positive probability under hardDist f xs; reason: a statement for every sample is a statement on the support
--   - encoding: [2n] with pairs (2i − 1, 2i) → Fin (2 * n), 0-based, pairs (2i, 2i + 1) for i : Fin n; reason: a relabelling of the indices
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Observation 4.3, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_xorLift
import Definitions.Def_RandomQueryXOR_hardDist

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- Observation 4.3 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.16 = PDF p.18): "For any y ∼ D_{f⊕}, g_{f⊕}(y) = f(x⋆_f). Further,
if i ∈ [n] is sensitive for x⋆_f with x⋆_f(i) = 0, then g(y ⊕ e_{2i}) = g(y ⊕ e_{2i−1}) = ¬f(x⋆_f)."

**Formalization Note** `y ∼ D_{f⊕}` is "`y` in the support of `hardDist f xs`"; `e_{2i−1}`, `e_{2i}`
flip `pairFst i`, `pairSnd i` (0-based). Stated for every `x⋆ = xs`, not only a
maximum-sensitivity input (the observation does not use maximality). -/
theorem observation_4_3 {n : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool)
    (y : Fin (2 * n) → Bool) (hy : 0 < (hardDist f xs).prob y) :
    xorLift f y = f xs ∧
      ∀ i ∈ sensZeros f xs,
        xorLift f (flip y (pairSnd i)) = !f xs ∧ xorLift f (flip y (pairFst i)) = !f xs := by sorry

end RandomQueryXOR
