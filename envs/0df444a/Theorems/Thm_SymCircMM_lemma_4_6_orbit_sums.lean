-- Prove2me | Theorems.Thm_SymCircMM_lemma_4_6_orbit_sums
-- name    : SymCircMM.lemma_4_6_orbit_sums
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:34.362236+00:00
-- url     : https://prove2.me/theorems/a8fca2f8-b598-47b0-a32a-8ffb77dd3c70
-- title:
--   Lemma 4.6 — a $G$-invariant combination of the gates of $M$ is a combination of the orbit sums $S_O$
-- statement:
--   Let $M$ be the multiplicative layer of a rigid bilinear $G$-symmetric circuit for $\mathrm{MM}_n$ (Proposition 4.2): each gate $g\in M$ computes $L(X)\,R(Y)$ with $L$ a linear form in the $A$-variables and $R$ a linear form in the $B$-variables, and $G$ acts on $M$, the image $\hat\sigma(g)$ computing $\sigma\cdot g$. Assume $\mathrm{char}(F)\nmid|G|$, and for an orbit $O\in M/G$ let $S_O=\sum_{g\in O}g$. If $f:A\times B\to F$ is $G$-invariant and is a linear combination of the functions computed by the gates of $M$, then $f$ is a linear combination of $\{S_O\mid O\in M/G\}$.
--
--   Applied to the outputs $C_{a,b}$, this gives display (5), the starting point of the utility count.
--
--   **Formalization Note** $M$ is any finite set with a $G$-action and gate data $L_m$, $R_m$ satisfying $L_{\sigma\cdot m}=L_m\circ(X\mapsto X\circ\sigma)$ and $R_{\sigma\cdot m}=R_m\circ(Y\mapsto\sigma\cdot Y)$; the rigid circuit of Proposition 4.2 gives such data.
--
--   Differences from the source:
--
--   - generalization: the multiplicative layer M of the rigid bilinear G-symmetric circuit C′, with features (i)–(iii) (PDF pp.10–11) → any finite G-set M with linear forms L m on A and R m on B, the gate m computing L m(X)·R m(Y), and L (σ•m) = L m ∘ (X ↦ X∘σ), R (σ•m) = R m ∘ (Y ↦ σ·Y); reason: the rigid circuit C′ of Proposition 4.2 gives such data (σ̂ acts on M and maps the A- and B-inputs of m to those of σ̂m); the proof uses only these features
--   - encoding: functions A × B → F → curried functions Matrix ι ι F → Matrix ι ι F → F (restrictions as functions on the product of the subspaces A_i × B_i); reason: Lean convention; the same functions
--   - encoding: char(F) ∤ |G| → (Nat.card G : F) ≠ 0; reason: a prime p divides m iff (m : F) = 0 in characteristic p, and (m : F) ≠ 0 for every m ≥ 1 in characteristic 0
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Lemma 4.6, p.12 (PDF p.13); proof Appendix C, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_SymCircMM_util

set_option autoImplicit false

namespace SymCircMM

/-- **Lemma 4.6** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.12 (PDF p.13); proof p.20 (PDF p.21)): "Let f : A × B → F be G-invariant
and a linear combination of the polynomials computed by the gates of M. Then f is a linear combination
of {S_O | O ∈ M/G}." Here `char F ∤ |G|` (§4.2) and `S_O = ∑_{g ∈ O} g`.

**Formalization Note.** The multiplicative layer `M` of the bilinear rigid `G`-symmetric circuit is a finite
`G`-set (rigidity makes the extension `σ̂` unique, feature (iii)); gate `m` computes `L m (X) · R m (Y)`
with `L m` an `A`-linear and `R m` a `B`-linear form (feature (i)), and `σ̂` maps the `A`-input of `m`
to that of `σ̂ m`: `L (σ • m) = L m ∘ (X ↦ X ∘ σ)`, likewise for `R` (the action (2) on matrices). Functions `A × B → F` are curried, `Matrix ι ι F → Matrix ι ι F → F`;
`orbitSum G L R m` is `S_O` for the orbit of `m`. -/
theorem lemma_4_6_orbit_sums {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Subgroup (Equiv.Perm ι)) (hG : (Nat.card G : F) ≠ 0)
    {M : Type} [Fintype M] [MulAction G M] (L R : M → Module.Dual F (Matrix ι ι F))
    (hL : ∀ (σ : G) (m : M), L (σ • m) = (L m).comp (colPerm (σ : Equiv.Perm ι)))
    (hR : ∀ (σ : G) (m : M), R (σ • m) = (R m).comp (rowPerm (σ : Equiv.Perm ι)))
    (f : Matrix ι ι F → Matrix ι ι F → F)
    (hf_inv : ∀ σ ∈ G, ∀ X Y, f (colPerm σ X) (rowPerm σ Y) = f X Y)
    (hf : f ∈ Submodule.span F (Set.range (gateForm L R))) :
    f ∈ Submodule.span F (Set.range (orbitSum G L R)) := by sorry

end SymCircMM
