-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_3_3
-- name    : TimeSpaceMA.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:08.36037+00:00
-- url     : https://prove2.me/theorems/736cee8c-77fb-4fd0-9474-2db1d0ed376f
-- title:
--   Lemma 3.3 — the lookup constraint $\Lambda$
-- statement:
--   Let $X$ be an $H\times H$ bit matrix. For all $r\in\mathbb Z^{2H}$ and $c\in\mathbb Z^H$,
--   $$\Lambda(r,c)\ge 0,$$
--   and $\Lambda(r,c)=0$ exactly when $r$ is the unit vector at some position $(a,o)$, $c$ is the unit vector at some position $b$, and $o=X_{ab}$.
--
--   This is how a chunk constraint checks a read of the input without containing the input bit in its variables.
--
--   Differences from the source:
--   - encoding: Λ(r, c) is a nonnegative integer → 0 ≤ Λ(r, c) in ℤ; reason: integrality is the type
--   - generalization: H, a power of 2 in the protocol → any natural number H; reason: the lemma on p.9 fixes no form of H and its proof uses none; powers of 2 are instances
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma 3.3, p.9

import Definitions.Def_TimeSpaceMA_lambdaForm

namespace TimeSpaceMA

/-- **Lemma 3.3** (Lookup constraint; Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…,
p.9). `Λ(r, c)` is nonnegative, and it vanishes exactly when `r` is the unit vector at some `(a, o)`, `c`
is the unit vector at some `b`, and `o = X_{ab}`.

**Formalization Note** "Integer" is the type `ℤ`. `H` is any natural number, not only a power of 2. -/
theorem lemma_3_3 {H : ℕ} (X : Fin H → Fin H → Bool) (r : Fin H × Bool → ℤ) (c : Fin H → ℤ) :
    0 ≤ lambdaForm X r c ∧
      (lambdaForm X r c = 0 ↔
        ∃ (a : Fin H) (o : Bool) (b : Fin H),
          r = Pi.single (a, o) 1 ∧ c = Pi.single b 1 ∧ o = X a b) := by sorry

end TimeSpaceMA
