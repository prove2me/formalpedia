-- Prove2me | Theorems.Thm_TorchFire_CGS_remark_4_20
-- name    : TorchFire.CGS.remark_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:39:47.458042+00:00
-- url     : https://prove2.me/theorems/69f1852f-bc69-47c6-82fc-ac95ee3a1876
-- title:
--   Remark 4.20, (27) — $\mathrm{Fire.Check}(\mathrm{enc}(\mathrm{forward},x),p)=1[O_2(\mathrm{enc}(\mathrm{forward},x),p)\ne\perp]$
-- statement:
--   The validity of a supplied tag can be checked with the public oracle $O_2$ by submitting the encoding of a forward query: for every oracle sample of Construction 4.18, every $x\in\{0,1\}^n$ and every tag $p$,
--   $$\mathrm{Fire.Check}(\mathrm{enc}(\mathrm{forward},x),p)=1\big[O_2(\mathrm{enc}(\mathrm{forward},x),p)\ne\perp\big]\quad(27),$$
--   because $P(x)$ never returns $\perp$.
--
--   In torch-fire every $\Gamma$ request carries the tag of the forward query $z_q$, so (27) lets the untelegraphability reduction (60) check tags through the public $O_2$.
--
--   Differences from the source:
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: any polynomially bounded ℓ ≥ r + k + 3 (21) → ℓ = r + k + 3; reason: the least allowed value; nothing depends on the choice
--   - encoding: a tag p ∈ {0,1}^r × {0,1}^µ × {0,1}^µ → a tag as held in registers, each hash value with the ⊥ flag of the response it came from; reason: Fire.Check is zero on malformed tags (p.27)
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Remark 4.20, (27), p.28; used as (60), p.57

import Mathlib
import Definitions.Def_TorchFire_CGS_Sample

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.CGS

/-- **Remark 4.20**, (27), p.28 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). The validity of a supplied tag can be checked with the public
oracle `O_2` by submitting the encoding of a forward query:
`Fire.Check(enc(forward, x), p) = 1[O_2(enc(forward, x), p) ≠ ⊥]` (`P(x)` never returns `⊥`), for every
oracle sample, `x ∈ {0,1}^n` and tag `p`. -/
theorem remark_4_20 (mu : ℕ) (ω : Sample mu) (x : Bits (n mu)) (p : TagIn mu) :
    checkIn ω (enc (.forward x)) p ↔ (O2 ω (enc (.forward x), p)).isSome = true := by sorry

end TorchFire.CGS
