-- Prove2me | Theorems.Thm_StretchDepth_testOf_mono
-- name    : StretchDepth.testOf_mono
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:49.953205+00:00
-- url     : https://prove2.me/theorems/5dd41229-4d3f-4bd8-a979-fcbd88f1183a
-- title:
--   Proof of Theorem 1 — $T_\rho$ is monotone in $\rho$
-- statement:
--   For partial assignments $\tau\supseteq\sigma$ and every $y$,
--   $$
--   T_\tau(y)\le T_\sigma(y).
--   $$
--   Assigning more values leaves fewer completions, hence fewer reachable outputs. In the proof this gives $T(y),T'(y)\le T^+(y)$.
--
--   Differences from the source:
--   - encoding: T_tau(y) <= T_sigma(y) as bits → T_tau(y) = true implies T_sigma(y) = true; reason: the same statement on {0, 1}
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Theorem 1, p.21

import Definitions.Def_StretchDepth_testOf

namespace StretchDepth

/-- **Proof of Theorem 1: `T_ρ` is monotone.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Theorem 1, p.21: "Note that for any pair of partial assignments τ ⊇ σ, we must have
Tτ(y) ≤ Tσ(y) for every y". -/
theorem testOf_mono {n N m M : ℕ} (H : Bits m → RoundTree n N M) (τ σ : PartialAssign n N)
    (hτσ : ExtendsPartial τ σ) (y : Bits M) (hy : testOf H τ y = true) :
    testOf H σ y = true := by sorry

end StretchDepth
