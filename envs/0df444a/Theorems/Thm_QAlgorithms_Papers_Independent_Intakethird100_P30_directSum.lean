-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_directSum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.directSum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:38:31.456898+00:00
-- url     : https://prove2.me/theorems/c790b53a-9ff8-411a-9d76-23179c5c68ad
-- title:
--   II A: concatenated-code tensor product and max threshold, (5)–(6)
-- statement:
--   Let $S$ be a finite nonempty set of blocks. For each $s\in S$, let $C_s$ be a nonempty code of distinct words on a finite nonempty coordinate register $D_s$, with finite label set $K_s$. Form the full Cartesian concatenation $C=\lvert C_s:s\in S\rvert$, labeled by $\prod_s K_s$, with coordinates $\coprod_sD_s$. For $0\le Q\le\tfrac12$, write $P_s(Q)$ and $P_C(Q)$ for the constructed Bob-only filtered operators. Under the explicit regrouping into corresponding Alice/Bob blocks,
--
--   $$P_C(Q)=\bigotimes_{s\in S}P_s(Q),\qquad
--   \mathrm{Ext}_B(P_C(Q))\Longleftrightarrow\forall s\in S,\ \mathrm{Ext}_B(P_s(Q)),\qquad
--   Q_C^*=\max_{s\in S}Q_{C_s}^*.$$
--
--   Here $Q_C^*$ is the upper boundary of nonextendable QBERs in $[0,\tfrac12]$, with value zero when none exist. The statement includes two codes and all finite nonempty iterates. Concatenation is a Cartesian product, and the constructed factors have positive trace.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 4, II A: concatenated-code tensor product and max threshold, (5)–(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.4, (5)–(6), including the finite iterated version: explicit block
regrouping yields the product coefficients and the maximum component threshold. -/
theorem directSum {S : Type} [Fintype S] [Nonempty S]
    {D M : S → Type} [∀ s, Fintype (D s)] [∀ s, Nonempty (D s)]
    [∀ s, Fintype (M s)] [∀ s, Nonempty (M s)]
    (C : (s : S) → M s → (D s → Bool)) (hC : ∀ s, Function.Injective (C s)) :
    (∀ Q : ℝ, 0 ≤ Q → Q ≤ 1 / 2 →
      (∀ (w w2 : Sigma D → Bool) (k l : (s : S) → M s),
        bobState (multiCode C) Q (w, k) (w2, l) =
          ∏ s, bobState (C s) Q ((fun i => w ⟨s, i⟩), k s)
            ((fun i => w2 ⟨s, i⟩), l s)) ∧
      (BobExtendible (bobState (multiCode C) Q) ↔
        ∀ s, BobExtendible (bobState (C s) Q))) ∧
    bobThreshold (multiCode C) = sSup (Set.range (fun s => bobThreshold (C s))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
