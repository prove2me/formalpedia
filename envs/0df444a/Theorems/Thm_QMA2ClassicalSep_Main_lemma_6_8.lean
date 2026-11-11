-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_lemma_6_8
-- name    : QMA2ClassicalSep.Main.lemma_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:47.06052+00:00
-- url     : https://prove2.me/theorems/75702e0a-a075-4995-85dc-8ce40f6bb8dd
-- title:
--   Lemma 6.8 — completion amplitudes: block compatibility, normalization, sign and fresh-entry identities
-- statement:
--   Let $k\ge2$ and let $(D,S)$ be a record (with $D$ a permutation database) and $|\mathrm{coords}(D)\cup S|<N/2$. Then:
--
--   1. **Block compatibility.** If $a_{D,S}(\theta)\ne0$, the two endpoints of every entry of $D$ lie in the same NO block of $\theta$.
--   2. **Normalization.** $\mathbb E_{\theta\sim\nu}|a_{D,S}(\theta)|^2=1$.
--   3. **Sign identity.** For every $e=(p;x\mapsto y)\in D$, $a_{D,S\triangle\partial e}(\theta)=s_\theta(x,y)\,a_{D,S}(\theta)$.
--   4. **Fresh-entry identity.** Let $I$ be a database, $e=(p;x\mapsto y)\notin I$ with $I\cup\{e\}$ a database, $|\mathrm{coords}(I\cup\{e\})\cup S|<N/2$, and
--   $$
--   \{y_A,y_B\}\cap(\mathrm{coords}(I)\cup S\cup\{x_A,x_B\})=\emptyset .
--   $$
--   Then $a_{I\cup\{e\},S}(\theta)=w_e(\theta)\,a_{I,S}(\theta)$.
--
--   These identities make the completion map $W$ norm-preserving on records and compatible with the sign queries (Lemma 6.9).
--
--   Differences from the source:
--   - reading: in (iv), the record whose size bound is assumed, and the weight w_e → the standing bound is assumed for the record (I ∪ {e}, S) (which implies it for (I, S)); w_e is the weight of Definition 6.6 for the oriented entry x ↦ y; reason: the lemma's hypothesis "for every record (D, S) with |coords(D) ∪ S| < N/2" applied to the records of (iv), as the proof uses it
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 34, Lemma 6.8 (proof pp. 34–35)

import Definitions.Def_QMA2ClassicalSep_Main_Completion

namespace QMA2ClassicalSep.Main

theorem lemma_6_8 (k : ℕ) (hk : 2 ≤ k) :
    (∀ (D : Finset (Entry k)) (S : Finset (HCoord k)), IsDatabase D → Admissible D S →
      (∀ θ : Labeling k, complAmp D S θ ≠ 0 → ∀ e ∈ D, SameBlock θ e.2.1 e.2.2) ∧
      (∑ θ : Labeling k, nu k * complAmp D S θ ^ 2 = 1) ∧
      (∀ e ∈ D, ∀ θ : Labeling k,
        complAmp D (symmDiff S (bdry e)) θ = (sθ θ e.2.1 e.2.2 : ℝ) * complAmp D S θ)) ∧
    (∀ (I : Finset (Entry k)) (e : Entry k) (S : Finset (HCoord k)),
      IsDatabase I → e ∉ I → IsDatabase (insert e I) → Admissible (insert e I) S →
      Disjoint ({Sum.inl e.2.2.1, Sum.inr e.2.2.2} : Finset (HCoord k))
        (coords I ∪ S ∪ {Sum.inl e.2.1.1, Sum.inr e.2.1.2}) →
      ∀ θ : Labeling k, complAmp (insert e I) S θ = wE θ e.2.1 e.2.2 * complAmp I S θ) := by sorry

end QMA2ClassicalSep.Main
