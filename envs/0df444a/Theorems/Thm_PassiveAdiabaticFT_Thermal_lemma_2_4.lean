-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_lemma_2_4
-- name    : PassiveAdiabaticFT.Thermal.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:41.703708+00:00
-- url     : https://prove2.me/theorems/bcd25ae5-922f-4198-a8a3-a7a36136c06f
-- title:
--   Lemma 2.4 — properties of dangerous syndromes
-- statement:
--   Let $C$ be a stabilizer code with a Pauli decoder, $D_\alpha$ the dangerous syndromes of $F_\alpha$ (Definition 2.3) and $\Pi_{D_\alpha}=\sum_{s\in D_\alpha}\Pi_s$. Then for every single-qubit Pauli $F_\alpha$:
--
--   1. $f_\alpha(D_\alpha)=D_\alpha$;
--   2. $[\Pi_{D_\alpha},F_\alpha]=0$;
--   3. every set $B\subseteq\Omega$ satisfying condition 1 of Definition 1.1, that is $[\hat O,P](I-\Pi_B)=0$ for every logical operator $O$ and single-qubit Pauli $P$, contains every $D_{\alpha'}$; and $\mathcal B_{\rm dec}=\bigcup_{\alpha'}D_{\alpha'}$ itself satisfies condition 1, so it is the smallest such set.
--
--   Items 1–2 make the good and bad syndrome sectors invariant under each Pauli error; item 3 identifies $\mathcal B_{\rm dec}$ with the minimal bad set of the rare-bad-syndrome property.
--
--   Differences from the source:
--   - generalization: item 3 assumes the code is thermally protected (Definition 1.1, conditions 1 and 2) → item 3 holds for every B ⊆ Ω satisfying condition 1, and ⋃_α D_α satisfies condition 1; reason: the proof uses condition 1 only; every bad set of a thermally protected code satisfies it
--   - encoding: f_α(D_α) = D_α → Finset.image (f α) (Dset α) = Dset α; reason: the same set equality
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 13, Lemma 2.4 (proof pp. 13–14)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Lemma 2.4 (p. 13): (1) `f_α(D_α) = D_α`; (2) `[Π_{D_α}, F_α] = 0`; (3) every set `B ⊆ Ω`
satisfying condition 1 of Definition 1.1 contains every `D_α`, and `⋃_α D_α` itself satisfies
condition 1, so it is the smallest such set. -/
theorem lemma_2_4 {b : ℕ} (C : StabCode b) (D : PauliDecoder C) (α : Fin b × Fin 3) :
    (D.Dset α).image (C.f α) = D.Dset α ∧
    C.projSet (D.Dset α) * Fα α = Fα α * C.projSet (D.Dset α) ∧
    (∀ B : Finset (Fin C.m → ZMod 2), D.BadSetCondition B → ∀ α' : Fin b × Fin 3, D.Dset α' ⊆ B) ∧
    D.BadSetCondition D.Bdec := by sorry

end PassiveAdiabaticFT.Thermal
