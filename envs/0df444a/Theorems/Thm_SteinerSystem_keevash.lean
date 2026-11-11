-- Prove2me | Theorems.Thm_SteinerSystem_keevash
-- name    : SteinerSystem.keevash
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-11T05:59:52.157349+00:00
-- url     : https://prove2.me/theorems/491439b8-4ad0-47a1-bddb-ebd432df8300
-- title:
--   Keevash's existence theorem
-- statement:
--   If $1\le t<k$, $(4k)^{90k(2k)^t(6\binom kt)^2} < n$ and $n$ satisfies the necessary condition of `SteinerSystem.param_dvd`, an $(n,k,t)$-Steiner system exists.
-- source:
--   Peter Keevash (2024), "A short proof of the existence of designs", https://arxiv.org/abs/2411.18291

import Definitions.Def_SteinerSystem

namespace SteinerSystem

open Filter in
theorem keevash {n k t : ℕ} (ht : 1 ≤ t) (hk : t < k)
    (hn : (4 * k) ^ (90 * k * (2 * k) ^ t * (6 * k.choose t) ^ 2) < n)
    (dn : ∀ i < t, (k - i).choose (t - i) ∣ (n - i).choose (t - i)) :
      Nonempty (SteinerSystem n k t) :=
  sorry

end SteinerSystem
