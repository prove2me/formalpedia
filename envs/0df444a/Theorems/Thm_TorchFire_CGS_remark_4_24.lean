-- Prove2me | Theorems.Thm_TorchFire_CGS_remark_4_24
-- name    : TorchFire.CGS.remark_4_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:44:59.959036+00:00
-- url     : https://prove2.me/theorems/76a1928a-62de-4192-9a8f-b778873f45fe
-- title:
--   Remark 4.24 — strong cloning correctness $\mathbb E[D(\mathrm{Fire.Clone}(|K\rangle\langle K|),|K\rangle\langle K|^{\otimes2})]\le\mathrm{negl}(\mu)$
-- statement:
--   Sample $O\leftarrow\mathrm{Fire.GenOracles}(1^\mu)$ and $(pk,sk)\leftarrow\mathrm{Fire.Setup}^O(1^\mu)$, put $s=pk$, and let $|K\rangle$ be the honest CGS flame (23). Then
--   $$\mathbb E\Big[D\big(\mathrm{Fire.Clone}^O(pk,s,|K\rangle\langle K|),\,|K\rangle\langle K|^{\otimes2}\big)\Big]\le\mathrm{negl}(\mu)\quad(29),$$
--   the expectation over oracle generation and setup.
--
--   Adapted from [ÇGS26, §9.4], without proof in the source. It is the CGS cloning error $e_{\mathrm{cl}}$ in torch-fire's cloning correctness.
--
--   Differences from the source:
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: any polynomially bounded ℓ ≥ r + k + 3 (21) → ℓ = r + k + 3; reason: the least allowed value; nothing depends on the choice
--   - encoding: OSS.Sign with intermediate measurements; U^O_{y,b} obtained from it by Fact 3.1 (Remark 4.12) → the deferred-measurement signing circuit written gate by gate; the zero state of Σ is |⊥⟩; reason: paper.md decisions 6 and 16
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Remark 4.24, (29), p.29 (adapted from [ÇGS26, §9.4])

import Mathlib
import Definitions.Def_TorchFire_CGS_tagErr
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS PPADSIS.SubexpSIS

namespace TorchFire.CGS

/-- **Remark 4.24** (strong cloning correctness, adapted from [ÇGS26, §9.4]), (29), p.29 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593).
Sample `O ← Fire.GenOracles(1^µ)` and `(pk, sk) ← Fire.Setup^O(1^µ)`, put `s = pk`, and let `|K⟩` be the
honest CGS flame (23). Then
`E[D(Fire.Clone^O(pk, s, |K⟩⟨K|), |K⟩⟨K|^{⊗2})] ≤ negl(µ)`, the expectation over oracle generation and
setup. The source cites [ÇGS26] and gives no proof. -/
theorem remark_4_24 :
    Negligible fun mu => avg (Sample mu) fun ω => avg (Bits (hl mu)) fun pk => cloneErr ω pk pk := by sorry

end TorchFire.CGS
