-- Prove2me | Theorems.Thm_RobustBoolPCSP_theorem_4_9
-- name    : RobustBoolPCSP.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:02.63365+00:00
-- url     : https://prove2.me/theorems/9b9d6f85-1826-4010-b203-4d263491deba
-- title:
--   Theorem 4.9 (Canonical perfect gaps) — $\{\mathsf A_k,\mathsf B_r\}$ and $\{\mathsf A_k,\mathsf C_t\}$
-- statement:
--   For every odd $k\ge3$, every $r\ge2$ and every $t\ge3$, both $\mathrm{fiPCSP}(\{\mathsf A_k,\mathsf B_r\})$ and $\mathrm{fiPCSP}(\{\mathsf A_k,\mathsf C_t\})$ have perfect integrality gaps, where
--
--   $$\mathsf A_k=(\mathrm{Ham}_k(\{\tfrac{k+1}2\}),\mathrm{NAND}_k),\quad\mathsf B_r=(\mathrm{Ham}_r(\{0,1\}),\mathrm{NAND}_r),\quad\mathsf C_t=(\mathrm{Ham}_t(\{1\}),\mathrm{Ham}_t(\{0,\dots,t\}\setminus\{t-1\})).$$
--
--   Each pair alone is robustly solvable, so these gaps are not consequences of the single-pair theorem of [BGS25].
--
--   Differences from the source:
--   - encoding: the template {A_k, B_r} → Template.pair with index Unit ⊕ Unit; reason: a two-element index set
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.3, Theorem 4.9, p.21 (pairs defined on p.21)

import Mathlib
import Definitions.Def_RobustBoolPCSP_SDP
import Definitions.Def_RobustBoolPCSP_Canonical

set_option autoImplicit false

namespace RobustBoolPCSP

/-- **Theorem 4.9 (Canonical perfect gaps)**, p.21. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"For every odd k ≥ 3, every r ≥ 2, and every t ≥ 3, both fiPCSP({Ak, Br}) and fiPCSP({Ak, Ct}) have
perfect integrality gaps." Here, for `k = 2b + 1`, `𝖠_k = (Ham_k({b + 1}), NAND_k)`,
`𝖡_r = (Ham_r({0, 1}), NAND_r)`, `𝖢_t = (Ham_t({1}), Ham_t({0, …, t} \ {t − 1}))` (p.21). -/
theorem theorem_4_9 (k r t : ℕ) (hk : Odd k) (hk3 : 3 ≤ k) (hr : 2 ≤ r) (ht : 3 ≤ t) :
    HasPerfectGap (templateAB k r) ∧ HasPerfectGap (templateAC k t) := by sorry

end RobustBoolPCSP
