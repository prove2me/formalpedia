-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_mult_agree_qtame
-- name    : PersistClust.Count.theorem_4_5_lemma_4_6_corrected_mult_agree_qtame
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T21:26:49.900557+00:00
-- url     : https://prove2.me/theorems/4e12af5b-7dbb-4762-99d4-3dfcc7e5fcb0
-- title:
--   Corrected Lemma 4.6 child (q-tame): diagrams agree on QNE_alpha after truncation
-- statement:
--   Let $X$ be a genuine $0$-dimensional persistence module given as a filtration of path components: $\mathrm{stage}:\mathbb{R}\to\mathrm{Set}\,\iota$ is a decreasing family of sets and $J_t$ is the "same component of $\mathrm{stage}(t)$" equivalence, compatible with the inclusions $\mathrm{stage}(t)\subseteq\mathrm{stage}(s)$ for $s\le t$ (`FiltrationLaw stage J`). Its rank function is $r(s,t)=\operatorname{rankFn}\,\mathrm{stage}\,J\,s\,t$ (the rank of $H_0(X_s)\to H_0(X_t)$, i.e. the number of components of $\mathrm{stage}(t)$ meeting $\mathrm{stage}(s)$), and its persistence diagram is the multiplicity function $D=\operatorname{mult}(r)$. Assume the module is q-tame: every structure rank is finite, $$\forall\, s,t\in\mathbb{R},\quad r(s,t)<\infty,$$ which is the paper's standing assumption on persistence modules of interest (for the superlevel-set filtrations of tame functions it follows from local finiteness of the component counts). The truncation at $\alpha$ is $\widetilde r_\alpha(s,t)=r(s,t)$ if $\alpha\le s$ and $\alpha\le t$, and $0$ otherwise (`truncRank r α`, Eq. (16) of Appendix A), giving the truncated diagram $\widetilde D_\alpha=\operatorname{mult}(\widetilde r_\alpha)$. $Q^{NE}_\alpha=(\alpha,+\infty]\times(\alpha,+\infty]$ is the closed north-east quadrant above $\alpha$.
--
--   This lemma asserts that, for a genuine q-tame module, the original diagram and its $\alpha$-truncation agree on $Q^{NE}_\alpha$:
--   $$\forall p\in Q^{NE}_\alpha,\quad \operatorname{mult}(r)(p)=\operatorname{mult}(\widetilde r_\alpha)(p).$$
--
--   The multiplicity of $p=(b,d)$ is defined as the infimum, over $0<\varepsilon<(b-d)/2$, of the bracket $\bigl(r(b-\varepsilon,d+\varepsilon)-r(b+\varepsilon,d+\varepsilon)\bigr)-\bigl(r(b-\varepsilon,d-\varepsilon)-r(b+\varepsilon,d-\varepsilon)\bigr)$, the number of classes born in $[b-\varepsilon,b+\varepsilon)$ dying in $[d-\varepsilon,d+\varepsilon)$. For $p\in Q^{NE}_\alpha$ all four probes at small $\varepsilon$ lie strictly above $\alpha$, where Eq. (18) makes the original and truncated ranks coincide; q-tameness makes every bracket $\mathbb{N}$-valued, the bracket is nondecreasing in $\varepsilon$ (the probe windows nest, by the window-count monotonicity facts M1–M3 that follow from `FiltrationLaw`), and an infimum of $\mathbb{N}$-valued terms is attained, so both infima agree.
--
--   The q-tameness hypothesis cannot be weakened to finiteness of the off-diagonal support $\{p:D(p)\ne0\}$: with a single bar carrying countably many classes at some point $(\beta,\delta)$ with $\delta<\alpha$ born above $b$, the two ranks entering the first bracket pair both become $\infty$ at every scale $\varepsilon\ge\varepsilon^*$, so the original bracket collapses by $\infty-\infty$ while the truncated one (which loses the below-$\alpha$ pair entirely) stays positive, and the support remains finite — the agreement genuinely fails. Q-tameness is exactly what excludes such collapsing bars and makes the diagram faithful.
--
--   **Formalization Note.** All notions live in `Definitions.Def_PersistClust_Count_Diagram` (namespace `PersistClust.Count`): `rankFn`, `mult` (the diagram of a rank function), `QNE`. `truncRank` is the shared Definition `PersistClust.Count.truncRank` (`Definitions.Def_PersistClust_Count_TruncRank`). `FiltrationLaw` is in `Definitions.Def_PersistClust_Count_FiltrationLaw`. The rank functions take values in $\mathbb{N}^\infty$, so q-tameness is stated as $r(s,t)\ne\top$. This is the Step 2 successor (q-tame form) of the corrected-Lemma-4.6 decomposition of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected`; it supersedes `PersistClust.Count.theorem_4_5_lemma_4_6_corrected_mult_agree`, whose finite-support statement is false.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), Appendix A (pp. 28–31) and the proof of Lemma 4.6 / corrected statement PersistClust.Count.theorem_4_5_lemma_4_6_corrected (pp. 20–21).

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

namespace PersistClust.Count

theorem theorem_4_5_lemma_4_6_corrected_mult_agree_qtame
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) (α : ℝ)
    (hQ : ∀ s t : ℝ, rankFn stage J s t ≠ ⊤) :
    ∀ p ∈ QNE α, mult (rankFn stage J) p = mult (truncRank (rankFn stage J) α) p := by sorry

end PersistClust.Count
