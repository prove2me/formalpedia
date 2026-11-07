-- Prove2me | Theorems.Thm_PCNonBool_fact_5_3
-- name    : PCNonBool.fact_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:46.458614+00:00
-- url     : https://prove2.me/theorems/4d4f625a-294b-4fad-8bed-b648cd77ebe8
-- title:
--   Fact 5.3 — a pigeon-degree lower bound for FPHP$(G)_{\mathrm{bool}}$ transfers to FPHP$(G)$ (char $\ne 2$)
-- statement:
--   **Fact 5.3.** Let $G=(U\sqcup V,E)$ be any bipartite graph and $\mathbb F$ a field of characteristic different from $2$, and let $D\in\mathbb R$. If every polynomial calculus refutation of FPHP$(G)_{\mathrm{bool}}$ over $\mathbb F$ has pigeon degree at least $D$, then every polynomial calculus refutation of FPHP$(G)$ over $\mathbb F$ has pigeon degree at least $D$.
--
--   The paper obtains this from the affine change of variables $x_{i,j}\mapsto1-2x_{i,j}$ between the $0/1$ and $\pm1$ encodings; it transfers the Boolean lower bound of Theorem 5.2 to the $\pm1$ encoding.
--
--   Differences from the source:
--   - encoding: "polynomial calculus requires pigeon degree D to refute P" → every refutation π of P satisfies D ≤ pdeg(π), D real; reason: the standard meaning of "requires degree D"
--   - reading: polynomial calculus (refutations on both sides of the statement) → the mission's PC model on both sides: lines reduced modulo the range axioms, axiom lines c·red(a) with c ∈ F, fan-in 2, refutation = derivation containing 1; reason: one PC model is used throughout the mission; it is the model the paper's own splitting and restriction steps (Lemmas 5.9, 5.13) need
--   - encoding: lines of a refutation represented in the quotient ring modulo the range axioms (p.11); size = number of monomials → lines are the multilinear representatives (redPM / redBool normal forms); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention (p.11); it only strengthens size and degree lower bounds
--   - encoding: refutation = derivation of the constant polynomial 1 → IsRefutation: a derivation that contains the line 1; reason: cutting a sequence after its first 1 gives a refutation in the paper's sense of no larger size or degree
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Fact 5.3, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_redPM
import Definitions.Def_PCNonBool_redBool
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_fphp
import Definitions.Def_PCNonBool_fphpBool
import Definitions.Def_PCNonBool_pdegSeq

namespace PCNonBool

/-- **Fact 5.3** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.27 (PDF p.30)). For any bipartite graph `G` and any field `F` of
characteristic `≠ 2`: if every refutation of FPHP(G)_bool over `F` has pigeon degree at least `D`,
then every refutation of FPHP(G) over `F` has pigeon degree at least `D`.

**Formalization Note** "PC requires pigeon degree D to refute P" is read as "every refutation of
`P` has pigeon degree `≥ D`". Both sides use the mission's PC model (`redBool` resp. `redPM`
normal forms, scalar-multiple axiom lines, refutations containing `1`). -/
theorem fact_5_3 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (hF : ringChar F ≠ 2)
    (G : BipGraph U V) (D : ℝ)
    (h : ∀ π : List (MvPolynomial (Var G) F), IsRefutation redBool (fphpBool G) π →
      D ≤ (pdegSeq G π : ℝ)) :
    ∀ π : List (MvPolynomial (Var G) F), IsRefutation redPM (fphp G) π →
      D ≤ (pdegSeq G π : ℝ) := by sorry

end PCNonBool
