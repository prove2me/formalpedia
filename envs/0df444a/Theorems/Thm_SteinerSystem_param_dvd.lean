-- Prove2me | Theorems.Thm_SteinerSystem_param_dvd
-- name    : SteinerSystem.param_dvd
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-11T05:57:29.785323+00:00
-- url     : https://prove2.me/theorems/017cd590-d450-428a-af61-4313c6252211
-- title:
--   Easy necessary condition for existence
-- statement:
--   If an $(n,k,t)$-Steiner system exists, $\binom{k-i}{t-i}$ divides $\binom{n-i}{t-i}$ for $0\le i<t$.

import Definitions.Def_SteinerSystem

namespace SteinerSystem

lemma param_dvd {n k t : ℕ} (ht : 1 ≤ t) (hk : t < k) (S : SteinerSystem n k t) :
    ∀ i < t, (k - i).choose (t - i) ∣ (n - i).choose (t - i) := by
  sorry

end SteinerSystem
