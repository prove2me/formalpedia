-- Prove2me | Theorems.Thm_RSCapacity_ListDecoding_Supplement_hyperplane_intersection
-- name    : RSCapacity.ListDecoding.Supplement.hyperplane_intersection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:18:43.601144+00:00
-- url     : https://prove2.me/theorems/0e99ebec-2b79-498b-afb8-9fdaa64aeaac
-- title:
--   Lemma 6.1 — the hyperplanes $H_j$, $j\in T\cup\{i\}$, meet only in $(\zeta_0,f_0)$
-- statement:
--   Let $F$ be a finite field, $k,n\ge0$, $\alpha_1,\dots,\alpha_n\in F$ distinct, and $u,v\in F^n$. Fix $\zeta_0\in F$ and $f_0\in F[X]$ with $\deg f_0<k$, and let $S_{\zeta_0}=\operatorname{agr}(u+\zeta_0v,f_0)=\{i:(u+\zeta_0v)(\alpha_i)=f_0(\alpha_i)\}$. Let $T\subseteq S_{\zeta_0}$ with $|T|=k$, let $g,h\in F[X]$ have degree $<k$ with $g(\alpha_t)=u_t$ and $h(\alpha_t)=v_t$ for all $t\in T$, and let $S=\{i:g(\alpha_i)=u_i,\ h(\alpha_i)=v_i\}$ be their correlated agreement set. For each $i$ let $H_i=\{(\zeta,f):\deg f<k,\ f(\alpha_i)=(u+\zeta v)(\alpha_i)\}$.
--
--   If $i\in S_{\zeta_0}\setminus S$, then
--
--   $$\bigcap_{j\in T\cup\{i\}}H_j=\{(\zeta_0,f_0)\}.$$
--
--   This is the first step of the pruning argument for Theorem 1.2: a single index of $S_{\zeta_0}$ outside the correlated agreement set, added to $T$, isolates the point $(\zeta_0,f_0)$, so that every $\zeta_0$ with $S\subsetneq S_{\zeta_0}$ can be indexed by a short sequence of hyperplane choices.
--
--   **Formalization Note** The vectors $u,v$ are indexed by `Fin n` (their values at $\alpha_i$). The hyperplanes are subsets of $F\times F[X]$ rather than of $F^{k+1}$; the condition $\deg f<k$ in each $H_j$ makes these the same sets. The polynomials $g,h$ are any degree-$<k$ interpolants on $T$; they are unique, so this is the source's choice.
--
--   Differences from the source:
--   - encoding: functions u, v : E → F_q and H_i ⊆ F_q^{k+1} → vectors Fin n → F and H_i ⊆ F × F[X] with deg f < k; reason: the identifications are bijections, same instances
--   - encoding: "the unique polynomials g, h of degree less than k such that g|T = u|T and h|T = v|T" → arbitrary degree-<k g, h with these interpolation properties; reason: with |T| = k distinct points such g, h are unique, so the hypotheses describe exactly the source's g, h
--   - reading: "T ⊂ S_ζ0" → T ⊆ S_ζ0; reason: the paper uses ⊂ for inclusion (it writes T ⊆ S ⊆ S_ζ0 immediately after, and |T| = k may equal |S_ζ0|)
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), Lemma 6.1, p.18 (setup §6.1 pp.17–18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Supplement_ProximityGaps

namespace RSCapacity.ListDecoding.Supplement

open RSCapacity.ListDecoding

/-- Lemma 6.1, submission #495 p.18, with the §6.1 setup (pp.17–18) as hypotheses:
`f₀` of degree `< k`, `T ⊆ S_{ζ₀}` with `|T| = k`, `g, h` of degree `< k` interpolating
`u, v` on `T`, and `i ∈ S_{ζ₀} \ S`. Then `⋂_{j ∈ T ∪ {i}} H_j = {(ζ₀, f₀)}`. -/
theorem hyperplane_intersection {F : Type} [Field F] [Fintype F] {n : ℕ} (k : ℕ)
    (α u v : Fin n → F) (hα : Function.Injective α)
    (ζ₀ : F) (f₀ : Polynomial F) (hf₀ : f₀.degree < (k : WithBot ℕ))
    (T : Finset (Fin n)) (hT : T ⊆ agreementSet α (u + ζ₀ • v) f₀) (hTcard : T.card = k)
    (g h : Polynomial F) (hg : g.degree < (k : WithBot ℕ)) (hh : h.degree < (k : WithBot ℕ))
    (hgT : ∀ t ∈ T, evaluation α g t = u t) (hhT : ∀ t ∈ T, evaluation α h t = v t)
    (i : Fin n) (hi : i ∈ agreementSet α (u + ζ₀ • v) f₀)
    (hiS : i ∉ correlatedAgreementSet α u v g h) :
    (⋂ j ∈ insert i T, lineHyperplane k α u v j) = {(ζ₀, f₀)} := by sorry

end RSCapacity.ListDecoding.Supplement
