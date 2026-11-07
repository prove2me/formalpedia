-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_2_1
-- name    : SublinearSteiner.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:04.177382+00:00
-- url     : https://prove2.me/theorems/5e79519d-06f5-4f20-88e5-c1c24febf7c0
-- title:
--   Lemma 2.1 — rank monotonicity and lifting
-- statement:
--   Let $T$ be the terminals, and let families of subsets of $T$ act as zero links.
--
--   1. For every threshold $a>0$, the decrease in the number of components of $G_a(T)$ caused by a family $\mathcal F$, given earlier links $Z$, does not increase when $a$ grows or when more earlier links are added: for $a\le a'$ and $Z\subseteq Z'$,
--   $$\kappa_{Z'}(a')-\kappa_{Z'\cup\mathcal F}(a')\le\kappa_Z(a)-\kappa_{Z\cup\mathcal F}(a).$$
--   2. The benefit is the integral of this decrease over $a$:
--   $$\mathrm{mst}(T,Z)-\mathrm{mst}(T,Z\cup\mathcal F)=\int_0^\infty\bigl(\kappa_Z(a)-\kappa_{Z\cup\mathcal F}(a)\bigr)\,da,$$
--   which at $Z=\emptyset$ is $B_T(\mathcal F)$.
--   3. If an edge set of weight $C_{\mathcal F}$ in the complete graph on $V$ connects each set of $\mathcal F$, then
--   $$L-\mathrm{OPT}\ge B_T(\mathcal F)-C_{\mathcal F}.$$
--
--   The lifting clause converts discounts on the MST weight into upper bounds on $\mathrm{OPT}$, and it is how the estimator's discounts are shown sound.
--
--   Differences from the source:
--   - reading: networks of total weight C_F connect each set of F → one edge set N of weight C_F in which each set of F is connected; reason: networks given per set have a union of weight at most their total, so this form covers them
--   - generalization: the benefit is the integral of the decrease → the same identity with arbitrary earlier links Z; reason: Z = ∅ is the printed statement; the proofs of Lemmas 4.1 and 4.2 use the marginal form
--   - encoding: a set of zero links → a family of subsets of T; reason: a pair is a two-element set; a benefit is defined for families on p.12
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 2.1, p.13

import Mathlib
import Definitions.Def_SublinearSteiner_ThresholdGraph

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 2.1 (Rank monotonicity and lifting), p.13. For every threshold `a`, the decrease of the number of
components of `G_a(T)` caused by a set of zero links, given a fixed set of earlier zero links, does not increase when `a`
grows or when more earlier links are added. The benefit is the integral of this decrease over `a`. Moreover, if networks
of total weight `C_F` connect each set of `F`, then `L − OPT ≥ B_T(F) − C_F`.

**Formalization Note.**
* Zero links are given as a family of subsets of `T`, each identified at zero cost; a set of link pairs is a family of two-element
  sets.
* The second clause carries earlier links `Z`; `Z = ∅` is the page's benefit `B_T(F)`. Integrability is in the conclusion.
* The networks are one edge set `N` in the complete graph on `V` with weight `C_F`. Networks given one per set have a
  union of weight at most their total, and that union connects each set, so this covers them. -/
theorem lemma_2_1 {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) :
    (∀ (Z Z' F : Finset (Finset (Fin n))), (∀ Y ∈ Z', Y ⊆ T) → (∀ Y ∈ F, Y ⊆ T) → Z ⊆ Z' →
      ∀ a a' : ℝ, 0 < a → a ≤ a' → rankDecrease w T a' Z' F ≤ rankDecrease w T a Z F) ∧
    (∀ (Z F : Finset (Finset (Fin n))), (∀ Y ∈ Z, Y ⊆ T) → (∀ Y ∈ F, Y ⊆ T) →
      MeasureTheory.IntegrableOn (fun a : ℝ => rankDecrease w T a Z F) (Set.Ioi 0) ∧
        contractedCost w T Z - contractedCost w T (Z ∪ F) =
          ∫ a in Set.Ioi (0 : ℝ), rankDecrease w T a Z F) ∧
    (∀ (F : Finset (Finset (Fin n))) (N : Finset (Sym2 (Fin n))) (OPT L : ℝ), (∀ Y ∈ F, Y ⊆ T) →
      IsSteinerOpt T w OPT → IsTerminalMST T w L →
      (∀ Y ∈ F, ∀ x ∈ Y, ∀ y ∈ Y, (edgeGraph N).Reachable x y) →
      benefitFamily w T F - w.weight N ≤ L - OPT) := by sorry

end SublinearSteiner
