-- Prove2me | Theorems.Thm_SemAC02_Supplement_lemma_7_4_php_boundary_expanders
-- name    : SemAC02.Supplement.lemma_7_4_php_boundary_expanders
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-18T14:48:18.405361+00:00
-- url     : https://prove2.me/theorems/700fead9-4c10-4023-be14-6b0099c2f0df
-- title:
--   Lemma 7.4 — Random boundary expanders for graph PHP
-- statement:
--   Let $\Delta_n=\lceil24\ln(2n)\rceil$ and $s_n=\lfloor n/(4\Delta_n)\rfloor$. For all sufficiently large $n$, sample a bipartite graph with $2n$ pigeons and $n$ holes by including each possible edge independently with probability $\Delta_n/n$. The probability that the graph is an $(s_n,\Delta_n/4)$-boundary expander, every pigeon has degree at most $2\Delta_n$, and every hole has degree at most $4\Delta_n$ tends to one as $n\to\infty$.
--
--   The finite weighted sum in the formal statement is precisely this product distribution on the edge indicators. The conclusions are the existing predicate `Lemma74Concl`. As in the source, the random model is used only for sufficiently large $n$, when $0\le\Delta_n/n\le1$; values at finitely many smaller $n$ do not affect the limit. No hypotheses or conclusions of Lemma 7.4 are changed.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems, https://www.doc.ic.ac.uk/~itzamere/Reslin_Simplification.pdf, Lemma 7.4, printed p.52 (PDF p.54), and Appendix D, printed p.73 (PDF p.75).

import Mathlib
import Definitions.Def_SemAC02_Supplement_phpG
open Filter Topology
attribute [local instance] Classical.propDecidable

namespace SemAC02.Supplement

 theorem lemma_7_4_php_boundary_expanders :
    Tendsto (fun n : ℕ =>
      ∑ x : (Fin n × Fin (2*n) → Bool),
        if Lemma74Concl ({Adj := fun u v => x (v,u)=true} : PCNonBool.BipGraph (Fin (2*n)) (Fin n))
        then ∏ e : Fin n × Fin (2*n),
          (if x e then (php74Delta n : ℝ)/n else 1-(php74Delta n : ℝ)/n)
        else 0) atTop (𝓝 1) := by sorry

end SemAC02.Supplement
