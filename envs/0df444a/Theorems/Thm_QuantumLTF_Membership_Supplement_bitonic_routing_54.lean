-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_bitonic_routing_54
-- name    : QuantumLTF.Membership.Supplement.bitonic_routing_54
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-25T01:54:48.059805+00:00
-- url     : https://prove2.me/theorems/959a2065-eab1-48e3-9eff-0ba8ae6b2030
-- title:
--   Reversible bitonic sorting with trace replay and classical-$m$ uniform prefix state preparation over $\mathrm{gates12}$
-- statement:
--   Establishes the existence of the `BitonicRouting54` reversible `gates12` circuit suite together with all correctness, trace-replay, size, and state-preparation theorems needed for second-to-first-quantization NSIL symmetrization.
--
--   1. **Bitonic Sort Correctness and Trace-Replay Algebra:** For any depth $d \in \mathbb{N}$, Boolean direction flag $\mathrm{asc}$, and length-$2^d$ array $x : \mathrm{Fin}(2^d) \to \alpha$ ordered by $\mathrm{key} : \alpha \to \kappa$, the Batcher bitonic sorting network output $\mathrm{sort}(\mathrm{key}, d, \mathrm{asc}, x)$ is a permutation of $x$ that is monotone when $\mathrm{asc} = \mathrm{true}$ and antitone when $\mathrm{asc} = \mathrm{false}$. The recorded trace length $\mathrm{sortTraceSize}(d)$ satisfies $4 \cdot \mathrm{sortTraceSize}(d) = d(d+1)2^d$, $\mathrm{routeSort}$ and $\mathrm{unrouteSort}$ are mutual inverses satisfying naturality under maps $f : \alpha \to \beta$, and replaying $\mathrm{sortTrace}(\mathrm{key}, d, \mathrm{asc}, x)$ recovers $\mathrm{sort}(\mathrm{key}, d, \mathrm{asc}, x)$.
--
--   2. **Reversible Sorting and Trace-Routing Circuits (`gates12`):** There exists a constant $C_{\mathrm{sort}} > 0$ (explicitly $C_{\mathrm{sort}} = 27$) and `gates12` (`LayeredCircuit`) constructions implementing:
--      - An integer comparator toggle `ltBitsCircuit w` of size $\le 20w + 1$ and controlled-swap circuit `cswapRegCircuit w` of size $7w$.
--      - Trace-controlled routing and unrouting circuits `routeSortCircuit d w` and `unrouteSortCircuit d w = (routeSortCircuit d w).adj`, each using at most $C_{\mathrm{sort}} \cdot 2^d (d+1)^2 (w+1)$ gates and implementing $|x, \mathrm{flags}\rangle \mapsto |\mathrm{routeSort}(d, \mathrm{flags}, x), \mathrm{flags}\rangle$ and its exact inverse.
--      - A reversible keyed bitonic record sorter `bitonicSortKeyCircuit d w_k w_p asc` on $2^d$ records of width $(w_k + w_p)$ bits using at most $C_{\mathrm{sort}} \cdot 2^d (d+1)^2 (w_k + w_p + 1)$ gates (together with a generic parameterized `sortWithTraceCircuit`). On clean trace and $w_k$-qubit comparator-ancilla wires, it maps $|x, 0^T, 0^{w_k}\rangle \mapsto |\mathrm{sort}(x), \mathrm{sortTrace}(x), 0^{w_k}\rangle$; moreover, its adjoint simultaneously unroutes arbitrary $w_p$-bit payloads sorted alongside $\mathrm{key}(k_{\mathrm{in}})$ and erases $\mathrm{sortTrace}$ cleanly back to $|0^T\rangle$.
--
--   3. **Controlled Classical-$m$ Uniform Prefix State Preparation:** There exists a constant $C_{\mathrm{unif}} > 0$ (explicitly $C_{\mathrm{unif}} = 25$) such that for all integers $b, m$ with $1 \le m \le 2^b$, `unifPrefixCircuit b m` uses at most $C_{\mathrm{unif}}(b+1)^2$ `gates12` gates (on $1 + b$ primary wires and $b$ clean ancilla wires), acts as the identity whenever the control bit is $|\mathrm{false}\rangle |v\rangle |0^b\rangle$, and prepares exact uniform amplitudes when the control bit is $|\mathrm{true}\rangle$:
--
--   $$
--   |\mathrm{true}\rangle |0^b\rangle |0^b\rangle \longmapsto \frac{1}{\sqrt{m}} \sum_{j=0}^{m-1} |\mathrm{true}\rangle |\mathrm{bin}_b(j)\rangle |0^b\rangle,
--   $$
--
--   with matching inverse action for `(unifPrefixCircuit b m).adj`.
--
--   This theorem supplies the complete reversible sorting, trace-unrouting, and controlled uniform state-preparation building blocks required for Alonso–Schott permutation preparation and Harmonic-Bucket symmetrization.
--
--   **Formalization Note** Both pure `Cslib.BitonicSort` theorems (ported from `cslib-frontier`) and the constructive `gates12` circuit implementations are packaged inside `Nonempty BitonicRouting54` defined in `Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54`.
-- source:
--   Batcher (1968), Sorting Networks and Their Applications; cslib-frontier Bitonic Sort & Trace (CslibFrontier/Algorithms/Lean/Sort/Bitonic/{Basic,ZeroOne,Correctness,Trace}.lean, Apache-2.0); Liu, Childs, Gottesman [LCG26] (arXiv:2411.04019, Section IV); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54

namespace QuantumLTF.Membership.Supplement

theorem bitonic_routing_54 : Nonempty BitonicRouting54 := by sorry

end QuantumLTF.Membership.Supplement
