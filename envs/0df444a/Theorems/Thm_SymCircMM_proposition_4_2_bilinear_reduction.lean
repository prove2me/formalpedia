-- Prove2me | Theorems.Thm_SymCircMM_proposition_4_2_bilinear_reduction
-- name    : SymCircMM.proposition_4_2_bilinear_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:37.454612+00:00
-- url     : https://prove2.me/theorems/05ba881f-238b-4ebf-814a-307d5184bea7
-- title:
--   Proposition 4.2 — reduction to a symmetric rigid bilinear circuit with $O(s)$ edges and at most $2s$ products
-- statement:
--   Let $G\le S_n$ act on the variables by (2). If $\mathrm{MM}_n$ is computed by a $G$-symmetric circuit $C$ of size $s$, then it is computed by a $G$-symmetric bilinear rigid circuit $C'$ of the form of Figure 1 with
--
--   $$\mathrm{size}(C')\le K\,s\qquad\text{and}\qquad \#\{\text{product gates of }C'\}\le 2s,$$
--
--   where $K$ is an absolute constant, independent of $n$, $F$, $G$ and $C$. If moreover $C$ is $G$-symmetric with output gates $\mathrm{out}$ in the sense of Definition 2.2 (one input gate per label, every extension fixing the outputs), then so is $C'$ with its output gates.
--
--   This reduction lets the lower bound argue on the layer of products $L\cdot R$ of a bilinear circuit on which $G$ acts.
--
--   **Formalization Note** $C'$ is a weighted circuit (field scalars on the edges into addition gates), as in the paper's construction. No assumption on the characteristic of $F$.
--
--   Differences from the source:
--
--   - encoding: the index set [n] = {1, …, n} → a finite type ι with n = card ι; reason: a relabelling of the index set
--   - encoding: an algebraic circuit (a finite labelled multi-DAG with designated output gates) and the polynomial ĝ ∈ F[X] of each gate → Circuit F X γ on a finite gate type γ (labels, edge multiplicities wire g c, a rank function for acyclicity); gate values in MvPolynomial X F; the output gates given by a map out : ι × ι → γ; reason: the same objects; "computing MM_n" is equality of polynomials at the designated output gates
--   - reading: C′ is a circuit in the sense of Definition 2.1 → C′ is a weighted circuit, with F-scalars on the edges into +-gates; its automorphisms and rigidity respect the scalars; reason: the proof builds C′ "with the displayed constants on the edges" (PDF p.21); in the plain model scaling needs constant gates and extra products, which a bilinear circuit cannot contain and which break the count 2s
--   - encoding: bilinear rigid circuit, of the form in Figure 1 (PDF p.11) → IsRigid ∧ IsBilinear ∧ IsFigure1: every product gate has exactly two children, each by one edge, an A-linear and a B-linear gate; reason: the paper's gloss right after the statement
--   - encoding: size(C′) = O(s) → ∃ K : ℕ before all other quantifiers with size(C′) ≤ K · s; reason: the definition of O(s), uniform in n, F, G and C
--   - generalization: C and C′ G-symmetric in the sense of Definition 2.2 → hypothesis: C IsGSymmetric (relaxed); conclusion: C′ IsGSymmetric, and C′ IsGSymmetricStrict with outputs out′ whenever C is IsGSymmetricStrict with outputs out; reason: the strict-to-strict part is the paper's statement; the relaxed part extends it to circuits with repeated input labels or no output condition, which the construction handles the same way
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Proposition 4.2, p.10 (PDF p.11); proof Appendix C, pp.18–20 (PDF pp.19–21)

import Mathlib
import Definitions.Def_SymCircMM_Circuit_IsGSymmetric
import Definitions.Def_SymCircMM_WCircuit_IsBilinear

set_option autoImplicit false

namespace SymCircMM

/-- **Proposition 4.2** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.10 (PDF p.11); proof Appendix C, pp.18–20 (PDF pp.19–21)):
"Let G ≤ S_n. If MM_n is computed by a G-symmetric circuit C of size s, then it is computed by a
G-symmetric bilinear rigid circuit C′ with size(C′) = O(s); moreover C′ has at most 2s product gates."
The paper adds that `C′` is "of the form in Figure 1".

**Formalization Note.** `C′` is a weighted circuit (scalars on the edges into `+`-gates, as in the proof:
"with the displayed constants on the edges"). `O(s)` is an absolute constant `K`, chosen before
`n`, `F`, `G` and `C`. No characteristic assumption. The hypothesis is the relaxed symmetry
`IsGSymmetric` (no output condition, repeated input labels allowed), and the conclusion gives `C′` the
same; in addition, when `C` is symmetric in the paper's sense with outputs `out` (`IsGSymmetricStrict`),
so is `C′` with outputs `out′`, which is the paper's statement. -/
theorem proposition_4_2_bilinear_reduction :
    ∃ K : ℕ, ∀ {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (G : Subgroup (Equiv.Perm ι))
      {γ : Type} [Fintype γ] (C : Circuit F (MMVar ι) γ) (out : ι × ι → γ),
      C.IsGSymmetric G → C.ComputesMMAt out →
      ∃ (γ' : Type) (_ : Fintype γ') (C' : WCircuit F (MMVar ι) γ') (out' : ι × ι → γ'),
        C'.IsGSymmetric G ∧ C'.IsRigid ∧ C'.IsBilinear ∧ C'.IsFigure1 ∧ C'.ComputesMMAt out' ∧
        C'.size ≤ K * C.size ∧ C'.numMul ≤ 2 * C.size ∧
        (C.IsGSymmetricStrict G out → C'.IsGSymmetricStrict G out') := by sorry

end SymCircMM
