-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_abelianHSP_standardAlgorithm_samples_annihilator
-- name    : QAlgorithms.DeWolf.abelianHSP_standardAlgorithm_samples_annihilator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:42:07.397817+00:00
-- url     : https://prove2.me/theorems/0b8a47c7-6061-46fd-a041-841b7554a36d
-- title:
--   Abelian HSP: the standard algorithm samples uniformly from H^⊥
-- statement:
--   This is the correctness statement of the standard quantum algorithm for the Abelian hidden subgroup problem.
--
--   Let $G = \mathbb Z_{N_1}\times\cdots\times\mathbb Z_{N_\ell}$ be a finite Abelian group written additively ($N_i \ge 1$), with characters $\chi_g(h) = \prod_{i=1}^{\ell} \omega_{N_i}^{g_i h_i}$, $\omega_N = e^{2\pi i/N}$, and quantum Fourier transform $F_G = F_{N_1}\otimes\cdots\otimes F_{N_\ell}$, $|k\rangle \mapsto |\chi_k\rangle = |G|^{-1/2}\sum_{g\in G}\chi_k(g)|g\rangle$. Let $S$ be a finite set, $H \le G$ a subgroup, and $f : G \to S$ a function hiding $H$:
--
--   $$f(g) = f(g') \iff g + H = g' + H.$$
--
--   The standard algorithm starts in $|0\rangle|0\rangle$ (registers of dimensions $|G|$ and $|S|$), prepares $|G|^{-1/2}\sum_{g}|g\rangle|0\rangle$, computes $f$ in superposition with one query, $|g\rangle|0\rangle\mapsto|g\rangle|f(g)\rangle$, (measures the second register,) applies $F_G$ to the first register and measures it. For every $g \in G$ the outcome $g$ occurs with probability
--
--   $$\Pr[\text{output } g] = \begin{cases} |H|/|G| & \text{if } \chi_g(h) = 1 \text{ for all } h\in H \ (\text{i.e. } \chi_g \in H^\perp),\\ 0 & \text{otherwise.}\end{cases}$$
--
--   Since $|H^\perp| = |G|/|H|$, the algorithm samples uniformly from the labels of the elements of $H^\perp$; each sample gives a linear constraint on $H$, which is how the algorithm generalizes Simon's algorithm, period finding and discrete logarithms.
--
--   **Formalization Note** The finite set $S$ is given an arbitrary additive group structure so that computing $f$ is the unitary $|g,b\rangle\mapsto|g,b+f(g)\rangle$, which maps $|g,0\rangle$ to $|g,f(g)\rangle$ as in the source. The intermediate measurement of the second register (step 4) is omitted: it does not change the distribution of the first register, so the output law is the first-register marginal of the state before the final measurement. The source's claim that $H$ can then be found efficiently from few samples is asserted without proof and is not part of this statement.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 60, §6.2.2. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Fourier
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- de Wolf §6.2.2 (PDF pp. 60–61), the standard algorithm for the Abelian hidden subgroup
problem. Let `G = ℤ_{N_1} × ⋯ × ℤ_{N_ℓ}`, let `S` be a finite set, `H ≤ G` a subgroup and
`f : G → S` constant on each coset of `H` and distinct on distinct cosets. Run the algorithm:
start in `|0⟩|0⟩`, create the uniform superposition over `G` in the first register, compute `f`
in superposition (one query), (measure the second register,) apply the QFT of `G` to the first
register and measure it. Then the output is `g` with probability `|H|/|G|` if `χ_g ∈ H^⊥`
(i.e. `χ_g(h) = 1` for all `h ∈ H`), and with probability `0` otherwise: the algorithm samples
uniformly from the labels of the elements of `H^⊥`. -/
theorem abelianHSP_standardAlgorithm_samples_annihilator {l : ℕ} (N : Fin l → ℕ)
    [∀ i, NeZero (N i)] {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
    (H : AddSubgroup ((i : Fin l) → ZMod (N i))) (f : ((i : Fin l) → ZMod (N i)) → S)
    (hf : AddHides f H) (g : (i : Fin l) → ZMod (N i)) :
    (g ∈ annihilator H →
      marginalFst (hspStandardState N f) g =
        (Nat.card H : ℝ) / (Fintype.card ((i : Fin l) → ZMod (N i)) : ℝ)) ∧
    (g ∉ annihilator H → marginalFst (hspStandardState N f) g = 0) := by
  sorry

end QAlgorithms.DeWolf
