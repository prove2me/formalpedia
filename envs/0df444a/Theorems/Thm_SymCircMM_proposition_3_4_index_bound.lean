-- Prove2me | Theorems.Thm_SymCircMM_proposition_3_4_index_bound
-- name    : SymCircMM.proposition_3_4_index_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:29:40.207195+00:00
-- url     : https://prove2.me/theorems/0e626651-eda8-4ec8-8ed6-aa01290d7de3
-- title:
--   Proposition 3.4 — $\sum_s\dim W_s\le[G:H]$ for inequivalent irreps with nonzero $H$-fixed vectors
-- statement:
--   Let $H\le G$ with $G$ finite, and let $W_1,\dots,W_m$ be pairwise inequivalent irreducible representations of $G$ over a field $F$ with $\mathrm{char}(F)\nmid|G|$, such that
--
--   $$W_s^H=\{u\in W_s\mid \forall h\in H,\ h\cdot u=u\}\ne\{0\}\qquad\text{for every } s\le m.$$
--
--   Then
--
--   $$\sum_{s=1}^m\dim(W_s)\le[G:H].$$
--
--   Applied to the stabiliser of a product gate, this gives Lemma 4.8.
--
--   Differences from the source:
--
--   - encoding: irreps W_1, …, W_m of G over F, pairwise inequivalent, with W_s^H ≠ 0 → finite-dimensional ρ s : Representation F G (V s) with IsIrreducible, no Representation.Equiv between ρ s and ρ t for s ≠ t, and some u ≠ 0 in V s fixed by every h ∈ H; reason: the same conditions; representations are finite dimensional by the convention of §3
--   - encoding: char(F) ∤ |G| → (Nat.card G : F) ≠ 0; reason: a prime p divides m iff (m : F) = 0 in characteristic p, and (m : F) ≠ 0 for every m ≥ 1 in characteristic 0
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Proposition 3.4, p.9 (PDF p.10); proof Appendix B, p.18 (PDF p.19)

import Mathlib

set_option autoImplicit false

namespace SymCircMM

/-- **Proposition 3.4** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.9 (PDF p.10); proof Appendix B, p.18 (PDF p.19)): "Let H ≤ G, and let
W_1, …, W_m be pairwise inequivalent irreps of G over F with char(F) ∤ |G|, such that
W^H_s := {u ∈ W_s | ∀h ∈ H, h · u = u} is nonzero for every s ≤ m. Then ∑^m_{s=1} dim(W_s) ≤ [G : H]."

**Formalization Note.** `G` is a finite group; `char F ∤ |G|` is `(|G| : F) ≠ 0`. The irreps are
finite-dimensional representations `ρ s` on `V s` (§3: representations are finite dimensional);
inequivalence is the absence of an equivalence of representations. -/
theorem proposition_3_4_index_bound {G : Type} [Group G] [Finite G] (H : Subgroup G)
    {F : Type} [Field F] (hG : (Nat.card G : F) ≠ 0) {m : ℕ} (V : Fin m → Type)
    [∀ s, AddCommGroup (V s)] [∀ s, Module F (V s)] [∀ s, FiniteDimensional F (V s)]
    (ρ : ∀ s, Representation F G (V s)) (hirr : ∀ s, (ρ s).IsIrreducible)
    (hineq : ∀ s t, s ≠ t → IsEmpty ((ρ s).Equiv (ρ t)))
    (hfix : ∀ s, ∃ u : V s, u ≠ 0 ∧ ∀ h ∈ H, ρ s h u = u) :
    ∑ s, Module.finrank F (V s) ≤ H.index := by sorry

end SymCircMM
