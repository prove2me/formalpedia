-- Prove2me | Theorems.Thm_TwinWidthI_GridThm_theorem_5_3
-- name    : TwinWidthI.GridThm.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:45.080164+00:00
-- url     : https://prove2.me/theorems/5ce90cef-17a4-4411-9b34-e6d837b02a28
-- title:
--   Theorem 5.3 (Marcus–Tardos, constant of Cibulka–Kynčl) — c_t·max(n,m) ones force a t-grid minor
-- statement:
--   Let $t\ge1$ and $c_t=\tfrac83(t+1)^2 2^{4t}$. Let $M$ be an $n\times m$ $0,1$-matrix with $n,m\ge1$. If $M$ has at least $c_t\max(n,m)$ entries equal to $1$, then $M$ has a $t$-grid minor, that is, a division of the rows into $t$ intervals and of the columns into $t$ intervals such that each of the $t^2$ zones contains an entry $1$:
--
--   $$\#\{(i,j): m_{i,j}=1\}\ \ge\ c_t\max(n,m)\ \Longrightarrow\ M\text{ has a }t\text{-grid minor}.$$
--
--   This is the Marcus–Tardos theorem (the key step in their proof of the Stanley–Wilf conjecture) with the constant obtained by Cibulka and Kynčl, as quoted in the paper. It is the single external ingredient of the Grid Minor Theorem for twin-width, used in Lemma 5.7.
--
--   **Formalization Note** The paper states "for every integer $t$, there is some $c_t$" and then quotes the Cibulka–Kynčl value $c_t=8/3(t+1)^22^{4t}$, which the proof of Lemma 5.7 and Theorem 5.4 use as "the $c_t$ of Theorem 5.3"; this explicit form is stated here. Added hypotheses: $t\ge1$ (a $0$-grid minor exists only for the empty matrix) and $n,m\ge1$ (for the $0\times0$ matrix the count hypothesis holds and no $t$-grid minor exists). Entries are `Bool`, `true` = 1.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:18, Theorem 5.3 (citing Marcus–Tardos [34]; constant of Cibulka–Kynčl [12])

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.GridThm

/-- Theorem 5.3, p. 3:18 (Marcus–Tardos, with the constant `c_t = 8/3 (t+1)^2 2^{4t}` of
Cibulka and Kynčl quoted on the same page): every `n × m` `0,1`-matrix with at least
`c_t · max(n, m)` entries `1` has a `t`-grid minor. -/
theorem theorem_5_3 (t n m : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin m) Bool)
    (hones : cMT t * (max n m : ℕ) ≤
      ((Finset.univ.filter (fun p : Fin n × Fin m => M p.1 p.2 = true)).card : ℝ)) :
    HasGridMinor M t := by sorry

end TwinWidthI.GridThm
