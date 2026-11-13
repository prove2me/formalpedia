-- Prove2me | Theorems.Thm_PPADSIS_SubexpSIS_searchRTC_spec
-- name    : PPADSIS.SubexpSIS.searchRTC_spec
-- status  : Proved
-- author  : @arka
-- created : 2026-11-13T05:39:33.313598+00:00
-- url     : https://prove2.me/theorems/93e55f6d-1f84-4469-9d00-2e6d824a7a6c
-- title:
--   Lemma 3.9 (circuit half) — exhaustive search is a polynomial-size regular tree circuit
-- statement:
--   Let $\varphi:\{0,1\}^n\to\{0,1\}$ be a well-formed Boolean circuit with exactly one output, of size $|\varphi|$ (input wires plus gates), and let $\Phi(\varphi)$ be the exhaustive-search tree circuit `PPADSIS_SubexpSIS_SearchRTC`. Then, for one constant exponent $k$ and every such $\varphi$:
--
--   1. $\Phi(\varphi)$ is a well-formed regular tree circuit in the sense of Definition 3.8;
--   2. its address length is $p=n$;
--   3. its size satisfies $|\Phi(\varphi)|\le(|\varphi|+2)^k$;
--   4. its output is the exhaustive-search result for $\varphi$:
--   $$u_\varepsilon\bigl(\Phi(\varphi)\bigr)=\begin{cases}(1,a^*)&\text{if some }a\in\{0,1\}^n\text{ has }\varphi(a)=1,\ \text{where }a^*\text{ is the lexicographically first such }a,\\(0,0^n)&\text{otherwise.}\end{cases}$$
--
--   This is the circuit half of Lemma 3.9: exhaustive search for the first satisfying assignment of $\varphi$ is the output of a regular tree circuit of size $\mathrm{poly}(|\varphi|)$ with address length $n$. Together with the polynomial-time computability of $\varphi\mapsto\Phi(\varphi)$ (`PPADSIS.SubexpSIS.searchRTC_polyTime`) it gives the milestone `PPADSIS.SubexpSIS.lemma_3_9`.
--
--   **Formalization Note** The output is compared with `searchOutput`, which writes $(1,a^*)$ as `true :: a*` and $(0,0^n)$ as `false :: 0^n`, and orders $\{0,1\}^n$ lexicographically through big-endian binary. The circuit $\varphi$ accepts $a$ when its output list is `[true]`.
-- source:
--   Arka Rai Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript), Lemma 3.9, p. 22 (with Definition 3.8, p. 22)

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_SearchRTC

namespace PPADSIS.SubexpSIS

theorem searchRTC_spec : ∃ k : ℕ, ∀ φ : Circuit, φ.WF → φ.outs.length = 1 →
    (searchRTC φ).WF ∧ (searchRTC φ).p = φ.nIn ∧ (searchRTC φ).size ≤ (φ.size + 2) ^ k ∧
      (searchRTC φ).output = searchOutput φ.nIn (fun a => φ.eval a = [true]) := by sorry

end PPADSIS.SubexpSIS
