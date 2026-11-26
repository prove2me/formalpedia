-- Prove2me | Theorems.Thm_PvsNP_unaryWidthClockPacket_linearTime
-- name    : PvsNP.unaryWidthClockPacket_linearTime
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T17:20:23.600401+00:00
-- url     : https://prove2.me/theorems/73ef6c58-aed0-48a6-b5b2-f4003609f96d
-- title:
--   Linear-time construction of a clipped and interleaved binary clock packet
-- statement:
--   A binary clock packet consists of $w$ leading ones, a zero separator, and a binary digit sequence. Its clipped representation begins with one bit recording whether any digit beyond the first $w$ is nonzero. The next $2w$ bits pair each of the first $w$ digits with a zero, padding the digit sequence with zeros when it is shorter than $w$. There is a finite-stack TM2 machine that computes this representation on every such packet and halts within $3n+4$ steps on every binary input of length $n$.
-- source:
--   Original machine and trace formalization for this packet format. For the surrounding binary Turing machine model, see S. Cook, The P versus NP Problem, Section 1, pp. 1–2, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf.

import Mathlib.Computability.TuringMachine.Computable

open Turing Computability

theorem PvsNP.unaryWidthClockPacket_linearTime :
  ∃ (f : List Bool → List Bool)
    (M : TM2ComputableInTime (id : List Bool → List Bool) (id : List Bool → List Bool) f),
    (∀ n : ℕ, M.time n = 3 * n + 4) ∧
    ∀ (w : ℕ) (bits : List Bool),
      f (List.replicate w true ++ false :: bits) =
        (bits.drop w).any id ::
          ((bits.take w ++ List.replicate (w - bits.length) false).flatMap
            (fun b => [b, false])) := by sorry
