-- Prove2me | Theorems.Thm_StabTestMem_affine_graph_soundness
-- name    : StabTestMem.affine_graph_soundness
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:11.820493+00:00
-- url     : https://prove2.me/theorems/b1afaf6e-2d2c-46e2-b169-20febfcd55b4
-- title:
--   Lemma 4.5 — conditional soundness of the affine-graph test
-- statement:
--   Fix a pure state $|\psi\rangle$ on $n=k+m$ qubits, a prefix $(a,r)\in\mathbb F_2^{2k}\times\mathbb F_2^m$ and a phase bit $\beta\in\mathbb F_2$, and let $P^\beta_{a,r}$ be the output distribution of Algorithm 3 on one copy. Let
--
--   $$A(a,r)=\max_{t\in\mathbb F_2^m}\big|\langle\psi|P_{a_Xr,\,a_Zt}|\psi\rangle\big| .$$
--
--   If $(s_1,b_1),\dots,(s_N,b_N)$ are $N$ independent samples from $P^\beta_{a,r}$, then
--
--   $$\Pr\big[\exists u\in\mathbb F_2^m,\ c\in\mathbb F_2:\ b_j=u\cdot s_j\oplus c\ \ \forall j\in[N]\big]\le 2^{m+1}\Big(\frac{1+A(a,r)}{2}\Big)^N .$$
--
--   When no completion of $(a,r)$ nearly stabilizes $|\psi\rangle$, $N=O(m)$ samples make passing the affine-graph test unlikely.
--
--   Differences from the source:
--   - encoding: n qubits with m = n − k → k + m qubits; reason: the same instances; the paper's m := n − k
--   - encoding: Pr over N independent samples → Σ over N-tuples in the event of the product of the probabilities (iidProb); reason: the product law
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.5, p. 30

import Definitions.Def_StabTestMem_hsProb
import Definitions.Def_StabTestMem_Aval
import Definitions.Def_StabTestMem_AffineConsistent
import Definitions.Def_StabTestMem_iidProb

namespace StabTestMem

open QAlgorithms

/-- **Lemma 4.5: conditional soundness of the affine-graph test.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.5, p. 30: "Fix
(a, r) ∈ F_2^{2k} × F_2^m and β ∈ F. Let P^β_{a,r} be the output distribution of Algorithm 3 on one
copy of |ψ⟩. Define A(a, r) := max_{t∈F_2^m} |⟨ψ| P_{a_X r, a_Z t} |ψ⟩|. Let (s_1, b_1), …, (s_N, b_N)
be N independent samples from P^β_{a,r}. Then Pr[∃u ∈ F_2^m, c ∈ F_2 such that b_j = u · s_j ⊕ c
for all j ∈ [N]] ≤ 2^{m+1} ((1 + A(a, r))/2)^N."

**Formalization Note.** `n = k + m`; `ψ` is a unit vector; `N = 0` is allowed (the bound is then
`2^{m+1} ≥ 1`). -/
theorem affine_graph_soundness {k m : ℕ} (ψ : EuclideanSpace ℂ (Qubits (k + m))) (hψ : IsState ψ)
    (a : CutRankSched.Pauli k) (r : Fin m → ZMod 2) (β : ZMod 2) (N : ℕ) :
    iidProb (hsProb ψ a r β) N AffineConsistent ≤
      (2 : ℝ) ^ (m + 1) * ((1 + Aval ψ a r) / 2) ^ N := by sorry

end StabTestMem
