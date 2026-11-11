-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_2_1
-- name    : SingleExpBisect.Main.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:41:45.31931+00:00
-- url     : https://prove2.me/theorems/5a877ea3-db7e-4a1f-8081-5e6b7bf3ba19
-- title:
--   Lemma 2.1 — at most 4^ℓ important connected S–T cuts of size ≤ ℓ, enumerable in O*(4^ℓ) time
-- statement:
--   Let $H$ be a graph on $n$ vertices and $S,T\subseteq V(H)$ disjoint with $H[S]$ connected (in particular $S\neq\emptyset$). Then
--
--   1. every connected $S$–$T$ cut $C$ is contained in an important connected $S$–$T$ cut $D$ with $|\delta_H(D)|\le|\delta_H(C)|$;
--   2. for every $\ell\ge0$ there are at most $4^\ell$ important connected $S$–$T$ cuts $D$ with $|\delta_H(D)|\le\ell$;
--   3. there are a constant $C$ and one deterministic machine that, on input $(H,\ell,S,T)$, outputs a list of exactly these cuts within $C\cdot4^\ell\cdot(n+1)^C$ steps.
--
--   Cited by the paper from Cygan et al., *Parameterized Algorithms* (2015), Theorems 8.11 and 8.13.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph → SimpleGraph (Fin n) with vertex set Fin n; reason: Lean convention; every such graph is isomorphic to one on Fin n
--   - encoding: S nonempty and connected → H[S] connected (Mathlib's Connected includes nonemptiness); reason: same condition
--   - encoding: "enumerated in O*(4^ℓ) time" → one TM2 machine on encodeInput H ℓ ++ encodeSet S ++ encodeSet T outputs encodeFamily L with L.toFinset the set of these cuts within C·4^ℓ·(n+1)^C steps, C fixed before the instance; reason: the paper names no machine; O* is a polynomial factor in the input size
--   - generalization: Lemma 2.1 states the count and the enumeration → a further conclusion: every connected S–T cut lies in an important one with no larger cut; reason: this is the sentence immediately before Lemma 2.1 (p. 13), used together with it in Lemma 3.11 and Claim 5.2; it adds a conclusion and drops nothing
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §2, p. 13, Lemma 2.1 (cited from [CFK+15, Theorems 8.11 and 8.13]) and the sentence before it

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §2, p. 13, Lemma 2.1 (cited from
[CFK+15, Theorems 8.11 and 8.13]), with the sentence before it: for disjoint `S, T` with `S`
nonempty and connected, every connected `S`–`T` cut lies in an important one with no larger cut;
for every `ℓ ≥ 0` there are at most `4^ℓ` important connected `S`–`T` cuts `D` with
`|δ_H(D)| ≤ ℓ`; and one machine enumerates them all within `C · 4^ℓ · (n + 1)^C` steps. -/
theorem lemma_2_1 :
    (∀ (n : ℕ) (H : SimpleGraph (Fin n)) (S T : Finset (Fin n)),
      Disjoint S T → (H.induce (S : Set (Fin n))).Connected →
      (∀ C : Finset (Fin n), IsConnCut H S T C →
          ∃ D : Finset (Fin n), IsImportantConnCut H S T D ∧ C ⊆ D ∧ cutSize H D ≤ cutSize H C) ∧
        ∀ ℓ : ℕ, ((Finset.univ : Finset (Finset (Fin n))).filter
          (fun D => IsImportantConnCut H S T D ∧ cutSize H D ≤ ℓ)).card ≤ 4 ^ ℓ) ∧
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (S T : Finset (Fin n)) (ℓ : ℕ),
        Disjoint S T → (H.induce (S : Set (Fin n))).Connected →
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (encodeInput H ℓ ++ encodeSet S ++ encodeSet T)
            (encodeFamily L) (C * 4 ^ ℓ * (n + 1) ^ C) ∧
          L.toFinset = (Finset.univ : Finset (Finset (Fin n))).filter
            (fun D => IsImportantConnCut H S T D ∧ cutSize H D ≤ ℓ) := by sorry

end SingleExpBisect.Main
