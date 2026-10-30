-- Prove2me | Theorems.Thm_SkipFreeFluct_MBI_theorem_5_4_calH_mbp
-- name    : SkipFreeFluct.MBI.theorem_5_4_calH_mbp
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T10:29:04.781992+00:00
-- url     : https://prove2.me/theorems/39a62aa2-eeb2-480b-82b2-67f8524b6df0
-- title:
--   Theorem 5.4 (MBP case), p. 15 — $\mathscr H^{[y}(x)=W(y-x-1)/y$ when $\beta=q=0$
-- statement:
--   Let $(X,\mathbb P)$ be a Markov branching process with immigration (MBI) with parameters $(\alpha,\mu,p,\beta,\nu,q)$ on $E=\{0,1,2,\dots\}$, with Q-matrix (5.1), branching mechanism $\psi$, immigration mechanism $\phi$, root $s_0$, and the sequences $W,\pi,\varpi$ of Lemma 5.1 (with $W(z)=0$ for $z\le -1$). For $x,y\ge 0$ let
--   $$\mathscr H^{[y}(x)=\sum_{l=0}^{y-x-1}\pi(y-x-1-l)\,\frac{(W\star\varpi)(l)}{l+x+1}\qquad(=0\text{ if }y\le x),$$.
--
--   If the MBI is a Markov branching process, i.e. $\beta=q=0$, then for all $x,y\ge0$
--   $$\mathscr H^{[y}(x)=\frac{W(y-x-1)}{y}.$$
--
--   This is the simplification of $\mathscr H^{[y}$ stated in Theorem 5.4 for MBPs, used in the MBP forms of items (1)–(3).
--
--   **Formalization Note** At $y=0$ the right-hand side is the undefined $0/0$ while the left-hand side is the empty sum $0$; Lean's convention $0/0=0$ makes the identity hold for all $x,y:\mathbb N$. $W(z)=0$ for $z\le-1$ is `Wz` on $\mathbb Z$. No validity hypothesis on the parameters is needed.
-- source:
--   Loeffen, Patie, Wang, Fluctuation Theory of Continuous-Time, Skip-Free Downward Markov Chains with Applications to Branching Processes with Immigration, arXiv:2208.14425v1, pp. 15–16, Theorem 5.4 (MBP simplification of ℋ^[y)

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
open scoped ENNReal Topology
open Filter MeasureTheory

namespace SkipFreeFluct.MBI

theorem theorem_5_4_calH_mbp (P : MBIParams) :
    IsMBP P → ∀ x y : ℕ, calH P y x = Wz P ((y : ℤ) - x - 1) / y := by sorry

end SkipFreeFluct.MBI
