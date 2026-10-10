-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_mult_agree
-- name    : PersistClust.Count.theorem_4_5_lemma_4_6_corrected_mult_agree
-- status  : Open
-- author  : @fabianroll
-- created : 2026-10-09T14:06:10.937177+00:00
-- url     : https://prove2.me/theorems/0233f077-7505-4acd-b349-59b5297c8a55
-- title:
--   Corrected Lemma 4.6 child: diagrams agree on QNE_alpha after truncation
-- statement:
--   Let $X$ be a genuine $0$-dimensional persistence module given as a filtration of path components: $\mathrm{stage}:\mathbb{R}\to\mathrm{Set}\,\iota$ is a decreasing family of sets and $J_t$ is the "same component of $\mathrm{stage}(t)$" equivalence, compatible with the inclusions $\mathrm{stage}(t)\subseteq\mathrm{stage}(s)$ for $s\le t$ (`FiltrationLaw stage J`). Its rank function is $r(s,t)=\operatorname{rankFn}\,\mathrm{stage}\,J\,s\,t$ (the rank of $H_0(X_s)\to H_0(X_t)$, i.e. the number of components of $\mathrm{stage}(t)$ meeting $\mathrm{stage}(s)$), and its persistence diagram is the multiplicity function $D=\operatorname{mult}(r)$. Assume $D$ has finite off-diagonal support ($\{p:D(p)\ne0\}$ is finite). The truncation at $\alpha$ is $\widetilde r_\alpha(s,t)=r(s,t)$ if $\alpha\le s$ and $\alpha\le t$, and $0$ otherwise (`truncRank r α`, Eq. (16) of Appendix A), giving the truncated diagram $\widetilde D_\alpha=\operatorname{mult}(\widetilde r_\alpha)$.
--
--   $Q^{NE}_\alpha=(\alpha,+\infty]\times(\alpha,+\infty]$ is the closed north-east quadrant above $\alpha$. This lemma asserts that, for a genuine module with finite diagram, the original diagram and its $\alpha$-truncation agree on $Q^{NE}_\alpha$:
--   $$\forall p\in Q^{NE}_\alpha,\quad \operatorname{mult}(r)(p)=\operatorname{mult}(\widetilde r_\alpha)(p).$$
--
--   The proof uses Eq. (18) — the truncated rank equals the original rank whenever both windows are at or above $\alpha$ — together with the $\eta$-grid of Eqs. (19)–(22) of Appendix A: the multiplicity of a point $p=(b,d)$ is an infimum of window-count differences, and for $p\in Q^{NE}_\alpha$ the windows probed at fine offsets $\eta$ lie above $\alpha$ where Eq. (18) makes the original and truncated ranks coincide, while the contributions of windows below $\alpha$ cancel in pairs (Eqs. (21)–(22)); the two infima are therefore equal. The required `rankFn` window-count monotonicity facts (antitone in the first argument, etc.) follow from `FiltrationLaw`.
--
--   **Formalization Note.** All notions live in `Definitions.Def_PersistClust_Count_Diagram` (namespace `PersistClust.Count`): `rankFn`, `mult` (the diagram of a rank function), `QNE`. `truncRank` is the shared Definition `PersistClust.Count.truncRank` (`Definitions.Def_PersistClust_Count_TruncRank`). `FiltrationLaw` is in `Definitions.Def_PersistClust_Count_FiltrationLaw`. This is Step 2 of the corrected-Lemma-4.6 decomposition of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected`.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), Appendix A (pp. 28–31) and the proof of Lemma 4.6 / corrected statement PersistClust.Count.theorem_4_5_lemma_4_6_corrected (pp. 20–21).

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

namespace PersistClust.Count

theorem theorem_4_5_lemma_4_6_corrected_mult_agree
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) (α : ℝ)
    (hFin : {p : EReal × EReal | (mult (rankFn stage J)) p ≠ 0}.Finite) :
    ∀ p ∈ QNE α, mult (rankFn stage J) p = mult (truncRank (rankFn stage J) α) p := by sorry

end PersistClust.Count
