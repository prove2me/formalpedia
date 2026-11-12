-- Prove2me | Theorems.Thm_TorchFire_TF_eq_87
-- name    : TorchFire.TF.eq_87
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:42:53.360229+00:00
-- url     : https://prove2.me/theorems/f870e64f-a8be-45e2-8c46-d25fe83f37ed
-- title:
--   (87) — the witness condition $(U_\Gamma-U_{\Gamma^0_i})(I-Q_i)=0$
-- statement:
--   Let $Q_i$ be the computational-basis diagonal projector onto the complete $\Gamma$-query inputs satisfying (86): $q'=(s',t,c,e,u)\in Q_{\mathrm{affine}}$, $s'=(\ell_i,a')$, $t\in T_{\mathrm{pub}}$ and $\mathrm{OSS.Ver}^{O_T}(t,M_T(s',t),\sigma_T)=1$. Outside its support either the request has a different label, or both affine oracles reject it. Consequently
--   $$(U_\Gamma-U_{\Gamma^0_i})(I-Q_i)=0\quad(87),$$
--   which is precisely the witness condition (65) of Lemma 8.2. It holds for every oracle sample and every label $\ell_i$.
--
--   Differences from the source:
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
--   - encoding: U_Γ and U_{Γ⁰_i} on the Γ query registers → the superposition oracles of the full public collection (47) with Γ and with Γ⁰_i, on its query and answer registers; reason: the other components are identical, so the difference is supported on Γ queries
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), (87), p.70; (85)–(86) p.70

import Mathlib
import Definitions.Def_TorchFire_TF_Sample

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- **The witness condition (87)**, p.70 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). Outside the support of `Q_i` (the diagonal projector
onto the `Γ`-query inputs satisfying (86) for the label `ℓ_i`), either the request has a different label,
or both affine oracles reject it. Consequently `(U_Γ − U_{Γ⁰_i})(I − Q_i) = 0`, as operators on the query
and answer registers of the public collection (47), for every oracle sample and label `ℓ_i`. -/
theorem eq_87 (lam R : ℕ) (ω : Sample lam R) (li : Label lam) :
    (xorOracle (pubOracle ω) - xorOracle (modOracle ω li)) * (1 - witnessProj ω li) = 0 := by sorry

end TorchFire.TF
