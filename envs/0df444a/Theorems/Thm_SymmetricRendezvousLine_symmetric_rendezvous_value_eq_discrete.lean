-- Prove2me | Theorems.Thm_SymmetricRendezvousLine_symmetric_rendezvous_value_eq_discrete
-- name    : SymmetricRendezvousLine.symmetric_rendezvous_value_eq_discrete
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:53:19.899767+00:00
-- url     : https://prove2.me/theorems/5582f2e3-137e-49f4-8c79-34efab5c491c
-- title:
--   Symmetric rendezvous: integer-time zigzag strategies suffice
-- statement:
--   **Theorem (Han–Du–Vera–Zuluaga).** Strategies in which the players move at maximum speed and change direction only at integer times dominate among all strategies; in particular
--   $$R=R_{\mathrm{disc}},$$
--   where $R_{\mathrm{disc}}$ is the infimum of $E(S,S)$ over mixed strategies $S$ all of whose paths are *integer zigzags*: paths starting at $0$ that, on each interval $[n,n+1]$ with $n\in\mathbb N$, move with constant velocity $+1$ or $-1$.
--
--   Here $R=\inf_S E(S,S)$ is the symmetric rendezvous value on the line: two players start at distance $2$, each with an independently random unknown orientation, both moving at speed at most $1$, both required to use the same mixed strategy $S$, and $E(S,S)$ is the expected first meeting time (see the definition file).
--
--   This reduces the continuous problem to a discrete one (a choice of $\pm1$ for each unit time step), which is the basis of the numerical bounds on $R$.
--
--   **Formalization Note** Only the equality of the two infima is asserted, which is the consequence of the dominance statement used to reduce the problem.
-- source:
--   Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line ("Han, Du, Vera, and Zuluaga [HDVZ] have shown that strategies in which the players move at maximum speed and only change direction at integer times dominate among all possible strategies - thus reducing this problem to a discrete one"); Q. Han, D. Du, J. C. Vera, L. F. Zuluaga, Improved bounds for the symmetric rendezvous search problem on the line, Operations Research 56(3) (2008).

import Definitions.Def_SymmetricRendezvousLine_defs

namespace SymmetricRendezvousLine

theorem symmetric_rendezvous_value_eq_discrete :
    symmetricRendezvousValue = discreteSymmetricRendezvousValue := by sorry

end SymmetricRendezvousLine
