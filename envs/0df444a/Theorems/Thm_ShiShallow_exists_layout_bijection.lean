-- Prove2me | Theorems.Thm_ShiShallow_exists_layout_bijection
-- name    : ShiShallow.exists_layout_bijection
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T06:25:19.465653+00:00
-- url     : https://prove2.me/theorems/7b839337-564b-443e-a6fb-cb697f7fa503
-- title:
--   A block-respecting bijection between the copy-major and role-major wire layouts
-- statement:
--   A register holding three copies of a verifier's wires plus one scratch wire can be relabelled bijectively onto a register laid out as input, then witness, then ancilla, then output, of the corresponding sizes. The relabelling is pinned down block by block: the first copy's input is the input block unchanged, the k-th copy's witness lands in the witness block at offset k times the witness width, the scratch wire becomes the output wire, and the remaining eight sub-blocks tile the ancilla block contiguously.
--
--   Without the block laws the statement would be empty, since the two registers have the same number of wires and any counting argument would supply some bijection. It is the block correspondence that makes the relabelling usable: results proved for a contiguous three-block arrangement can be transported through it to the layout that a verifier family is required to have.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem exists_layout_bijection (n wit anc : ℕ) :
    ∃ σ : Fin (3 * (n + (wit + (anc + 1))) + 1)
        → Fin (n + (3 * wit + ((2 * n + 3 * anc + 3) + 1))),
      Function.Bijective σ
      -- copy 1 input  ↦ role input block, offset 0
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = j → (σ v).val = j)
      -- copy 1 witness ↦ role witness block, offset 0 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = n + j → (σ v).val = n + j)
      -- copy 1 ancilla ↦ role ancilla block, offset 0
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = n + wit + j → (σ v).val = n + 3 * wit + j)
      -- copy 1 output  ↦ role ancilla block, offset anc
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = n + wit + anc → (σ v).val = n + 3 * wit + anc)
      -- copy 2 input   ↦ role ancilla block, offset anc + 1
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = (n + (wit + (anc + 1))) + j →
          (σ v).val = n + 3 * wit + anc + 1 + j)
      -- copy 2 witness ↦ role witness block, offset 1 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = (n + (wit + (anc + 1))) + n + j → (σ v).val = n + wit + j)
      -- copy 2 ancilla ↦ role ancilla block, offset n + anc + 1
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = (n + (wit + (anc + 1))) + n + wit + j →
          (σ v).val = 2 * n + 3 * wit + anc + 1 + j)
      -- copy 2 output  ↦ role ancilla block, offset n + 2 * anc + 1
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = (n + (wit + (anc + 1))) + n + wit + anc →
          (σ v).val = 2 * n + 3 * wit + 2 * anc + 1)
      -- copy 3 input   ↦ role ancilla block, offset n + 2 * anc + 2
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = 2 * (n + (wit + (anc + 1))) + j →
          (σ v).val = 2 * n + 3 * wit + 2 * anc + 2 + j)
      -- copy 3 witness ↦ role witness block, offset 2 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = 2 * (n + (wit + (anc + 1))) + n + j → (σ v).val = n + 2 * wit + j)
      -- copy 3 ancilla ↦ role ancilla block, offset 2 * n + 2 * anc + 2
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = 2 * (n + (wit + (anc + 1))) + n + wit + j →
          (σ v).val = 3 * n + 3 * wit + 2 * anc + 2 + j)
      -- copy 3 output  ↦ role ancilla block, offset 2 * n + 3 * anc + 2
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = 2 * (n + (wit + (anc + 1))) + n + wit + anc →
          (σ v).val = 3 * n + 3 * wit + 3 * anc + 2)
      -- scratch wire   ↦ role output wire
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = 3 * (n + (wit + (anc + 1))) →
          (σ v).val = 3 * n + 3 * wit + 3 * anc + 3) := by
  sorry

end ShiShallow
