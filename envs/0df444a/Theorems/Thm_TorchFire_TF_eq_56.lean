-- Prove2me | Theorems.Thm_TorchFire_TF_eq_56
-- name    : TorchFire.TF.eq_56
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:47:31.611677+00:00
-- url     : https://prove2.me/theorems/82f2a4f4-e09b-40c9-89fa-b5bc430845ba
-- title:
--   (56) — one cloning call: $D(\rho_{T'F_0F_1},|T_t\rangle\langle T_t|\otimes|F_s\rangle\langle F_s|^{\otimes2})\le e_{\mathrm{cl}}+4L\sqrt d$
-- statement:
--   Fix the oracles with a successful setup, an honest serial $s=(\ell,a)$ and a published torch key $t=t_j$. Let $\rho_{T'F_0F_1}$ be the output of $\mathrm{TF.Clone}^O(pk,t,s,\cdot)$ on $|T_t\rangle\langle T_t|\otimes|F_s\rangle\langle F_s|$, where $|F_s\rangle=|A_a\rangle\otimes|K\rangle$ is the honest flame (40). Then
--   $$D\big(\rho_{T'F_0F_1},\,|T_t\rangle\langle T_t|\otimes|F_s\rangle\langle F_s|^{\otimes2}\big)\le e_{\mathrm{cl}}+4L\sqrt d\quad(56),$$
--   with $e_{\mathrm{cl}}$ the CGS cloning error of $\mathrm{Fire.Clone}^{O_K}(0^\mu,0^\mu,\cdot)$ on $|K\rangle\langle K|$ (51) and $d$ as in (53). (The output registers are ordered $F_0$, then $T',F_1$.)
--
--   This is the one-call step of Theorem 7.7's cloning-correctness proof; the induction over calls (57) and the averaging (58) give (33).
--
--   Differences from the source:
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: OSS.Sign with intermediate measurements; U^O_{y,b} obtained from it by Fact 3.1 (Remark 4.12) → the deferred-measurement signing circuit written gate by gate; the zero state of Σ is |⊥⟩; reason: paper.md decisions 6 and 16
--   - encoding: Dig : {0,1}* → {0,1}^L (14) → Dig uniform on {0,1}^{≤ 1+λ+2Lr}; reason: paper.md decision 10; every message signed in torch-fire has length 1+λ+2Lr
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
--   - reading: "≤ e_cl + 4L√d = negl(λ)" → the pointwise bound ≤ e_cl + 4L√d for fixed oracles; reason: "= negl(λ)" is the averaged consequence through (52) and (55), stated in the goal (33) and in Lemma 7.6 (55)
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §7.2, proof of Theorem 7.7, step 2, (56), p.56

import Mathlib
import Definitions.Def_TorchFire_TF_cloneTF

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- **One cloning call, (56)**, §7.2 (proof of Theorem 7.7), step 2, p.56 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). For fixed oracles
with a successful setup, an honest serial `s = (ℓ, a)` and a published torch key `t = t_j`, the output
`ρ_{T′F_0F_1}` of `TF.Clone^O(pk, t, s, ·)` on `|T_t⟩⟨T_t| ⊗ |F_s⟩⟨F_s|` (with
`|F_s⟩ = |A_a⟩ ⊗ |K⟩`) satisfies
`D(ρ_{T′F_0F_1}, |T_t⟩⟨T_t| ⊗ |F_s⟩⟨F_s|^{⊗2}) ≤ e_cl + 4L√d`,
with `e_cl` the CGS cloning error of `Fire.Clone^{O_K}(0^µ, 0^µ, ·)` on `|K⟩⟨K|` (51) and `d` of (53). The
output registers are ordered `F_0, (T′, F_1)`. -/
theorem eq_56 (lam R : ℕ) (ω : Sample lam R) (hω : SetupOK ω) (s : Serial lam) (j : Fin R) :
    traceDist
      (cloneTF ω (tk ω j) s (ketbra fun x : AReg lam × Flame lam =>
        longKeyState (OT ω) (tk ω j) x.1 *
          (longKeyState (OA ω s.1) s.2 x.2.1 * CGS.flameVec (OK ω) x.2.2)))
      (ketbra fun x : Flame lam × (AReg lam × Flame lam) =>
        (longKeyState (OA ω s.1) s.2 x.1.1 * CGS.flameVec (OK ω) x.1.2) *
          longKeyState (OT ω) (tk ω j) x.2.1 *
          (longKeyState (OA ω s.1) s.2 x.2.2.1 * CGS.flameVec (OK ω) x.2.2.2)) ≤
      CGS.cloneErr (OK ω) 0 0 + 4 * L lam * Real.sqrt (dErr ω s) := by sorry

end TorchFire.TF
