-- Prove2me | Theorems.Thm_PreservePast_theorem_9
-- name    : PreservePast.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:42:21.423204+00:00
-- url     : https://prove2.me/theorems/e212694d-4766-478a-a9ba-0bf279560a6f
-- title:
--   Theorem 9 — a complete-class finite upper bound (deterministic code)
-- statement:
--   Let $K\ge1$, $1\le r\le m$, $R\ge1$, $\epsilon>0$, $\xi\ge0$, and let $W_0\in\mathbb R^{m\times n}$ be any checkpoint. Then there is a **deterministic** code of width
--   $$
--   B\le K\Big[N_1\big(n,n,2,\tfrac{\epsilon}{2R^2}\big)+\min\Big\{N_1\big(m,n,\sqrt2,\tfrac{\epsilon}{4R\sqrt r}\big),\ N_2\big(m,n,\sqrt2,\tfrac{\epsilon}{4R}\big)\Big\}\Big]
--   $$
--   that, for every history of $K$ old tasks and every promised query $(x,p)$ (rank $r$, radius $R$), returns an update of rank at most $r$, Frobenius norm at most $R$, fit $\tfrac12\|Hx-p\|^2\le\xi$ and loss increment at most $\epsilon$ on every task. In particular $B_{\mathrm{full}}(K,n,m,r;\epsilon,\xi,R,\beta)$ is at most this width. Here $N_p$ is the code length of Lemma 4.
--
--   This coefficient code is the baseline the paper improves on, and it supplies the two extreme rank ranges ($r=1$ and $r>\epsilon^{-2}$) of the upper bound of Theorem 4.
--
--   **Formalization Note** The bound on $B_{\mathrm{full}}$ is stated by exhibiting the deterministic code (`DetAchieves`), as the theorem's last sentence says.
--
--   Differences from the source:
--   - encoding: B_full ≤ K[…]; the code is deterministic and supports every promised query → some deterministic code of width B ≤ K[…] succeeds for every history and every promised query; reason: this is the theorem's own two sentences; it implies B_full ≤ K[…] since a deterministic code is a protocol
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.1, p.17 (PDF p.19), Theorem 9, (43)

import Mathlib
import Definitions.Def_PreservePast_DetAchieves
import Definitions.Def_PreservePast_Ncode

namespace PreservePast

/-- **Theorem 9 (a complete-class finite upper bound).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.1, p.17 (PDF p.19): "Let K ≥ 1,
1 ≤ r ≤ m, R ≥ 1, ϵ > 0, and ξ ≥ 0. Then
B_full ≤ K[N₁(n, n, 2, ϵ/(2R²)) + min{N₁(m, n, √2, ϵ/(4R√r)), N₂(m, n, √2, ϵ/(4R))}]. (43)
The code is deterministic and supports every promised query."

For every checkpoint `W₀ ∈ ℝ^{m×n}` there is a deterministic code with at most the width (43)
that succeeds (14) for every history of `K` tasks and every promised query (13).

**Formalization Note.** `B_full ≤ b` is stated by exhibiting a deterministic code (`DetAchieves`)
of some width `B ≤ b`, as the theorem's last sentence says; `N_p` is `Ncode p` of Lemma 4. -/
theorem theorem_9 {m n : ℕ} (W₀ : Matrix (Fin m) (Fin n) ℝ) (K r : ℕ) (R ε ξ : ℝ)
    (hK : 1 ≤ K) (hr : 1 ≤ r) (hrm : r ≤ m) (hR : 1 ≤ R) (hε : 0 < ε) (hξ : 0 ≤ ξ) :
    ∃ B : ℕ, B ≤ K * (Ncode 1 n n 2 (ε / (2 * R ^ 2)) +
        min (Ncode 1 m n (Real.sqrt 2) (ε / (4 * R * Real.sqrt r)))
          (Ncode 2 m n (Real.sqrt 2) (ε / (4 * R)))) ∧
      ∃ (enc : (Fin K → Task W₀) → Fin (2 ^ B))
        (dec : Fin (2 ^ B) → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
        DetAchieves enc dec r ε ξ R := by sorry

end PreservePast
