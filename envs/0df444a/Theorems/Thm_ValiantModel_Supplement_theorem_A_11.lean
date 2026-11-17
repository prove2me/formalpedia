-- Prove2me | Theorems.Thm_ValiantModel_Supplement_theorem_A_11
-- name    : ValiantModel.Supplement.theorem_A_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:26:24.875736+00:00
-- url     : https://prove2.me/theorems/0eced695-32ec-47f9-a81f-2423be093c1f
-- title:
--   Theorem A.11, p.54 — a VC-2 class whose 1-point closure class has infinite VC dimension
-- statement:
--   There exist a countably infinite domain $X$ and a hypothesis class $H\subseteq\{0,1\}^X$ such that
--   $$\mathrm{VC}(H)=2\qquad\text{but}\qquad \mathrm{VC}\big(\mathrm{Cl}_1(H)\big)=\infty,$$
--   where $\mathrm{Cl}_1(H)=\{\mathrm{Closure}(V(p,H)):p\in X\}$ is the 1-point closure class.
--
--   On $\{0,1\}^d$ the $k$-query closure class has VC dimension at most $(d+1)(k+1)$ (Lemma 4.8). This theorem shows that no such bound in terms of the VC dimension of the class holds on an infinite domain, already for $k=1$.
--
--   Differences from the source:
--   - encoding: countably infinite → `Countable X ∧ Infinite X`; reason: the standard meaning
--   - encoding: VC dimension → the ℕ∞-valued published `vcDim`; infinite is `⊤`; reason: Definition 9
--   - encoding: Closure(V(p, H)) for every p ∈ X → points with V(p, H) = ∅ contribute no member; reason: Closure is defined only for non-empty families (p.54); in the paper's witness every V(p, H) is non-empty
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Theorem A.11, p.54 (PDF p.56); proof pp.54–55 (PDF pp.56–57)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_ValiantModel_Supplement_OnePointClosure

open HighDimProb.Chaining

namespace ValiantModel.Supplement

/-- **Theorem A.11**, Hanneke, Mehrotra, Velegkas, Zampetakis, arXiv:2605.13840 (version held, sha256
f793f255…), p.54 (PDF p.56): there are a countably infinite domain `X` and a class `H ⊆ {0,1}^X` with
`VC(H) = 2` whose 1-point closure class `Cl₁(H) = {Closure(V(p, H)) : p ∈ X}` has infinite VC
dimension.

**Formalization Note.** "Countably infinite" is `Countable X ∧ Infinite X`; `VC` is the `ℕ∞`-valued
`vcDim`, so infinite VC dimension is `⊤`. -/
theorem theorem_A_11 :
    ∃ X : Type, Countable X ∧ Infinite X ∧
      ∃ H : Set (X → Bool), vcDim H = 2 ∧ vcDim (onePointClosureClass H) = ⊤ := by sorry

end ValiantModel.Supplement
