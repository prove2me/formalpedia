-- Prove2me | Theorems.Thm_TalagrandConc_Chromatic_theorem_9_1
-- name    : TalagrandConc.Chromatic.theorem_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:50.079985+00:00
-- url     : https://prove2.me/theorems/0b0fc6ea-a22c-4656-b88c-b7c134c5b876
-- title:
--   Theorem 9.1 — $P(\chi(G(n,p),m)\in[a-k,a])\ge1-2e^{-t^2/8}-P(\sup_{\mathrm{card}F\le t\sqrt m}\chi(G(n,p),F)>k)$
-- statement:
--   Let $G(n,p)$ be the random graph on $V=\{1,\dots,n\}$ in which each of the possible edges $(i,j)$, $i<j$, is present with probability $p$, $0<p<1$, independently of the others. For $A\subseteq V$ let $\chi(G,A)$ be the chromatic number of the subgraph induced on $A$, and $\chi(G,m)=\inf\{\chi(G,A);\ \operatorname{card}A=m\}$.
--
--   Let $m\le n$ and $k$ be natural numbers and $t>0$. Then there exists an integer $a$ such that
--   $$P\big(\chi(G(n,p),m)\in[a-k,a]\big)\ \ge\ 1-2e^{-t^2/8}-P\big(\sup\{\chi(G(n,p),F);\ F\subset V,\ \operatorname{card}F\le t\sqrt m\}>k\big).$$
--
--   The theorem says that $\chi(G(n,p),m)$ is concentrated on an interval of $k+1$ consecutive integers, up to an error $2e^{-t^2/8}$ plus the probability that some set of at most $t\sqrt m$ vertices already needs more than $k$ colours. The last term vanishes when $k>t\sqrt m$, and remains small for smaller $k$ when $p=n^{-\alpha}$.
--
--   **Formalization Note** $G(n,p)$ is realised as the graph $G(x)$ of a configuration $x\in\{0,1\}^{E_0}$ under the product of Bernoulli($p$) laws. The hypothesis $m\le n$ is implicit on the page ($\chi(G,m)$ is an infimum over $m$-subsets of $V$); without it $\chi(G,m)=+\infty$ and the statement fails. The integer $a$ may depend on $n,p,m,k,t$. Probabilities are real numbers (`Measure.real`), so the right-hand side may be negative, as on the page.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 163, Theorem 9.1, Eq. (9.1)

import Mathlib
import Definitions.Def_TalagrandConc_Chromatic_Basic

open MeasureTheory
open scoped Classical

namespace TalagrandConc.Chromatic

theorem theorem_9_1 (n m k : ℕ) (p t : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (ht : 0 < t)
    (hm : m ≤ n) :
    ∃ a : ℤ,
      1 - 2 * Real.exp (-t ^ 2 / 8)
          - (gnp n p).real {x | (k : ℕ∞) < localSup (graphOf x) (t * Real.sqrt m)}
        ≤ (gnp n p).real {x | (((a - k : ℤ)) : WithTop ℤ) ≤ chiMZ (graphOf x) m ∧
            chiMZ (graphOf x) m ≤ (a : WithTop ℤ)} := by sorry

end TalagrandConc.Chromatic
