-- Prove2me | Theorems.Thm_PPADSIS_SubexpSIS_lemma_3_9
-- name    : PPADSIS.SubexpSIS.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:48:03.985194+00:00
-- url     : https://prove2.me/theorems/5d692b81-f2f7-42e2-9215-f8cb7a57d89b
-- title:
--   Lemma 3.9 — exhaustive search as a polynomial-size regular tree circuit, computed in polynomial time
-- statement:
--   There is a polynomial-time algorithm that, given a Boolean circuit $\varphi:\{0,1\}^n\to\{0,1\}$, outputs a regular tree circuit $C_\varphi$ with address length $p=n$ and
--   $$|C_\varphi|\le\mathrm{poly}(|\varphi|),$$
--   whose output is $(1,a^*)$ for the lexicographically first $a^*\in\{0,1\}^n$ with $\varphi(a^*)=1$, and $(0,0^n)$ if $\varphi$ is unsatisfiable.
--
--   Formally: there are a map $\Phi$ from circuits to regular tree circuits, computed in polynomial time on descriptions, and an exponent $k$, such that for every well-formed circuit $\varphi$ with $n$ inputs and one output, $\Phi(\varphi)$ is a well-formed regular tree circuit with $p=n$, $|\Phi(\varphi)|\le(|\varphi|+2)^k$, and output equal to the exhaustive-search output of $a\mapsto[\varphi(a)=1]$.
--
--   The lemma shows that regular tree circuits, whose description is short even when the tree has exponentially many leaves, can perform exhaustive search; §7.3 uses it to make the SIS puzzle tree-structured.
--
--   Differences from the source:
--   - encoding: "a polynomial-time algorithm, given a Boolean circuit" → a map on circuits computed in polynomial time on circuit descriptions (`PolyTimeOn`), defined on every circuit value; reason: the paper fixes no representation, and an algorithm can reject ill-formed codes in polynomial time.
--   - encoding: $|C_\varphi|\le\mathrm{poly}(|\varphi|)$ → $|C_\varphi|\le(|\varphi|+2)^k$ for one $k$; reason: the standard form of a polynomial bound.
--   - encoding: the pair $(s,w)$ → the bit string $s\,w$, and "lexicographically first" → least big-endian value among strings of length $n$; reason: the same order on strings of equal length.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 22, Lemma 3.9

import Mathlib
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_PPADSIS_SubexpSIS_RegularTreeCircuit

namespace PPADSIS.SubexpSIS

theorem lemma_3_9 :
    ∃ Φ : Circuit → RTC, PPSLattice.PolyTimeOn Circuit.enc (fun φ => (Φ φ).enc) ∧
      ∃ k : ℕ, ∀ φ : Circuit, φ.WF → φ.outs.length = 1 →
        (Φ φ).WF ∧ (Φ φ).p = φ.nIn ∧ (Φ φ).size ≤ (φ.size + 2) ^ k ∧
        (Φ φ).output = searchOutput φ.nIn (fun a => φ.eval a = [true]) := by sorry

end PPADSIS.SubexpSIS
