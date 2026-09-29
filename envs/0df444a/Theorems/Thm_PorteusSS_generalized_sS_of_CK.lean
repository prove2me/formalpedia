-- Prove2me | Theorems.Thm_PorteusSS_generalized_sS_of_CK
-- name    : PorteusSS.generalized_sS_of_CK
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:57:16.901338+00:00
-- url     : https://prove2.me/theorems/ad92c335-4d48-4951-9501-85adcc0ac62b
-- title:
--   Theorem 2 — if every $G_{cn}$ is in $C(K_c)$ and $Y_n(x) \neq \emptyset$, a generalized $(s,S)$ policy is optimal in period $n$
-- statement:
--   Consider the inventory model of §§II–III under its standing assumptions (concave increasing ordering cost $c$ with $c(0) = 0$ and limit pairs $(c_0,K_0)$, $(c_\infty,K_\infty)$; $0 \le \alpha \le 1$; one-sided Pólya demand density $\varphi$; PF-integrable, bounded-below holding-and-shortage cost $m$). Fix a period $n \ge 1$ and suppose
--
--   1. $G_{\kappa n} = \kappa\cdot + h_n \in C(K_\kappa)$ for every slope $\kappa \in C$, and
--   2. $Y_n(x)$ is nonempty for every $x \in \mathbb R$.
--
--   Then a generalized $(s,S)$ policy is optimal in period $n$: there exist $s, S \in \mathbb R$ and a generalized $(s,S)$ policy $y$ with
--   $$ y(x) \in Y_n(x) \quad \text{for all } x \in \mathbb R . $$
--
--   This theorem converts the functional property of the single-period functions $G_{\kappa n}$ into the structure of the optimal ordering rule; Lemma 3 supplies its hypotheses.
--
--   **Formalization Note.** $G_{\kappa n}$ is defined by eq. (7), $\kappa y + h_n(y)$. The standing assumptions on $\alpha$, $\varphi$ and $m$ are included because they are the paper's standing assumptions for every statement about the model; the paper's proof of Theorem 2 uses only those on $c$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 415, Theorem 2

import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Theorem 2 (p. 415). In the model of §§II–III, if for a period `n ≥ 1` every
`G_{κ n} = κ· + h_n` (`κ ∈ C`) lies in `C(K_κ)` and `Y_n(x)` is nonempty for every `x`,
then a generalized `(s, S)` policy is optimal in period `n`. -/
theorem generalized_sS_of_CK (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (n : ℕ) (hn : 1 ≤ n)
    (hG : ∀ κ ∈ slopeSet c, CK (Kc c κ) (Gfn c m φ f0 α κ n))
    (hY : ∀ x : ℝ, (Yset c m φ f0 α n x).Nonempty) :
    ∃ s S : ℝ, ∃ pol : ℝ → ℝ, IsGenSS pol s S ∧ ∀ x : ℝ, pol x ∈ Yset c m φ f0 α n x := by sorry

end PorteusSS
